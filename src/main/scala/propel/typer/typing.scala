package propel
package typer

import ast.*
import util.*


extension (expr: Term)
  inline def typed: (Term, Option[Type]) =
    let(expr.withIntrinsicInfo(Typing.Term)) { case expr -> Typing(tpe) => expr -> tpe }
  def untyped: Term = Typing.Term.strip(expr) match
    case term @ Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe, expr.untyped)
    case term @ App(properties, expr, arg) => App(term)(properties, expr.untyped, arg.untyped)
    case term @ TypeAbs(ident, expr) => TypeAbs(term)(ident, expr.untyped)
    case term @ TypeApp(expr, tpe) => TypeApp(term)(expr.untyped, tpe)
    case term @ Data(ctor, args) => Data(term)(ctor, args map { _.untyped })
    case term @ Var(_) => term
    case term @ Cases(scrutinee, cases) => Cases(term)(scrutinee.untyped, cases map { (pattern, expr) => pattern.untyped -> expr.untyped })

extension (pattern: Pattern)
  inline def typed: (Pattern, Option[Type]) =
    let(pattern.withIntrinsicInfo(Typing.Pattern)) { case pattern -> Typing(tpe) => pattern -> tpe }
  def untyped: Pattern = Typing.Pattern.strip(pattern) match
    case pattern @ Match(ctor, args) => Match(pattern)(ctor, args map { _.untyped })
    case pattern @ Bind(_) => pattern


case class Typing(tpe: Option[Type]) extends Enrichment(Typing)

object Typing extends Enrichment.Intrinsic[Pattern | Term, Typing]:
  private case class Context(vars: Map[Symbol, Type], typeVars: Set[Symbol]) extends Enrichment(Context)

  private object Context extends Enrichment.Extrinsic[Term, Context]


  case class Specified(tpe: Either[Set[Symbol], Type]) extends Enrichment(Specified)

  object Specified extends Enrichment.Extrinsic[Pattern | Term, Specified]


  def strip(construct: Pattern | Term) = construct match
    case construct: Pattern => Pattern.strip(construct)
    case construct: Term => Term.strip(construct)

  def make(construct: Pattern | Term) = construct match
    case construct: Pattern => Pattern.make(construct)
    case construct: Term => Term.make(construct)

  object Pattern extends Enrichment.Intrinsic[Pattern, Typing]:
    def strip(pattern: Pattern) = pattern.withoutInfo(Typing, Specified, Context)

    def make(pattern: Pattern) = pattern match
      case Match(ctor, args) =>
        let(pattern.info(Specified)) { specified =>
          val unfolded = specified flatMap {
            case Specified(Right(tpe: Recursive)) => unfold(tpe)
            case Specified(Right(tpe)) => Some(tpe)
            case _ => None
          }
          val result = (unfolded collect {
            case Sum(sum) =>
              sum collectFirst { case (`ctor`, tpes) if tpes.size == args.size =>
                val (typedArgs, argInfos) = (args zip tpes map { (arg, tpe) =>
                  arg.withExtrinsicInfo(Specified(Right(tpe))).typed
                }).unzip
                if argInfos forall { _.nonEmpty } then
                  Match(pattern)(ctor, typedArgs) -> Typing(Some(Sum(List(ctor -> (argInfos map { _.get })))))
                else
                  Match(pattern)(ctor, typedArgs) -> Typing(None)
              }
          }).flatten
          result getOrElse Match(pattern)(ctor, args) -> Typing(None)
        }

      case Bind(ident) =>
        pattern -> Typing(pattern.info(Specified) collect { case Specified(Right(tpe)) => tpe })
  end Pattern

  object Term extends Enrichment.Intrinsic[Term, Typing]:
    def strip(expr: Term) = expr.withoutInfo(Typing, Specified, Context)

    def make(expr: Term) =
      val context = expr.info(Context) getOrElse Context(Map.empty, Set.empty)
      val term = expr.withoutInfo(Context)

      def vars(pattern: Pattern): Map[Symbol, Type] = pattern match
        case Match(_, args) => (args flatMap vars).toMap
        case Bind(ident) => pattern.info(Specified) match
          case Some(Specified(Right(tpe))) => Map(ident -> tpe)
          case _ => Map.empty

      term match
        case Abs(properties, ident, tpe, expr) =>
          let(tpe.syntactic) { (tpe, tpeSyntactic) =>
            let(context.copy(vars = context.vars + (ident -> tpe))) { context =>
              let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
                val typeVars = term.info(Specified) match
                  case Some(Specified(Left(tpe))) => context.typeVars ++ tpe
                  case _ => context.typeVars

                val specified = Specified(Left(typeVars))

                if wellDefined(tpe) && (tpeSyntactic.freeTypeVars -- typeVars).isEmpty then
                  Abs(term)(properties, ident, tpe, expr).withExtrinsicInfo(specified) -> Typing(exprType map { Function(tpe, _) })
                else
                  term.withExtrinsicInfo(specified) -> Typing(None)
              }
            }
          }
        case App(properties, expr, arg) =>
          let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
            let(arg.withExtrinsicInfo(context).typed) { (arg, argType) =>
              val unfolded = exprType flatMap {
                case tpe: Recursive => unfold(tpe)
                case tpe => Some(tpe)
              }
              val result = unfolded collect {
                case Function(arg, result) if argType exists { conforms(_, arg) } => result
              }
              App(term)(properties, expr, arg) -> Typing(result)
            }
          }
        case TypeAbs(ident, expr) =>
          let(context.copy(typeVars = context.typeVars + ident)) { context =>
            let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
              TypeAbs(term)(ident, expr) -> Typing(exprType map { Universal(ident, _) })
            }
          }
        case TypeApp(expr, tpe) =>
          let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
            let(tpe.syntactic) { (tpe, tpeSyntactic) =>
              val typeVars = term.info(Specified) match
                case Some(Specified(Left(tpe))) => context.typeVars ++ tpe
                case _ => context.typeVars

              val specified = Specified(Left(typeVars))

              val unfolded = exprType flatMap {
                case tpe: Recursive => unfold(tpe)
                case tpe => Some(tpe)
              }
              val result = unfolded collect {
                case Universal(ident, result) => subst(result, Map(ident -> tpe))
              }

              if wellDefined(tpe) && (tpeSyntactic.freeTypeVars -- typeVars).isEmpty then
                TypeApp(term)(expr, tpe).withExtrinsicInfo(specified) -> Typing(result)
              else
                TypeApp(term)(expr, tpe).withExtrinsicInfo(specified) -> Typing(None)
            }
          }
        case Data(ctor, args) =>
          let((args.withExtrinsicInfo(context) map { _.typed }).unzip) { (args, argsInfos) =>
            val argsTypes = argsInfos.sequenceIfDefined
            Data(term)(ctor, args) -> Typing(argsTypes map { tpes => fold(Sum(List(ctor -> tpes))) })
          }
        case Var(ident) =>
          val tpe = context.vars get ident orElse { term.info(Specified) collect { case Specified(Right(tpe)) => tpe } }
          (tpe map { tpe => term.withExtrinsicInfo(Specified(Right(tpe))) } getOrElse term) -> Typing(tpe)
        case Cases(scrutinee, cases) =>
          let(scrutinee.withExtrinsicInfo(context).typed) { (scrutinee, scrutineeType) =>
            scrutineeType match
              case Some(scrutineeType) =>
                val (typedCases, patternsTypes, exprsTypes) = (cases map { (pattern, expr) =>
                  val (typedPattern, patternType) =
                    pattern.withExtrinsicInfo(Specified(Right(scrutineeType))).typed

                  if patternType.nonEmpty then
                    let(context.copy(vars = context.vars ++ vars(typedPattern))) { context =>
                      let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
                        (typedPattern -> expr, patternType, exprType)
                      }
                    }
                  else
                    (typedPattern -> expr, None, None)
                }).unzip3

                val patternType = patternsTypes.sequenceIfDefined flatMap { _ reduceLeftIfDefined { join(_, _) } }

                if patternType exists { conforms(scrutineeType, _) } then
                  val exprType = exprsTypes.sequenceIfDefined flatMap { _ reduceLeftIfDefined { join(_, _) } }
                  Cases(term)(scrutinee, typedCases) -> Typing(exprType)
                else
                  Cases(term)(scrutinee, cases) -> Typing(None)

              case _ =>
                Cases(term)(scrutinee, cases) -> Typing(None)
          }
  end Term
end Typing
