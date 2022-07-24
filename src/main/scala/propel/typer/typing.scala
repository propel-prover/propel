package propel
package typer

import ast.*
import util.*

case class Typing(tpe: Option[Type]) extends Enrichment(Typing)

object Typing extends Enrichment.Intrinsic[Pattern | Term, Typing]:
  private case class Context(vars: Map[Symbol, Type], typeVars: Set[Symbol]) extends Enrichment(Context)

  private object Context extends Enrichment.Extrinsic[Term, Context]


  case class Specified(tpe: Type) extends Enrichment(Specified)

  object Specified extends Enrichment.Extrinsic[Pattern | Term, Specified]


  def make(construct: Pattern | Term) = construct match
    case construct: Pattern => Pattern.make(construct)
    case construct: Term => Term.make(construct)

  object Pattern extends Enrichment.Intrinsic[Pattern, Typing]:
    def make(pattern: Pattern) = pattern match
      case Match(ctor: Constructor, args: List[Pattern]) =>
        let(pattern.info(Specified)) { specified =>
          val unfolded = specified flatMap {
            case Specified(tpe: Recursive) => unfold(tpe)
            case Specified(tpe) => Some(tpe)
          }
          val result = (unfolded collect {
            case Sum(sum) =>
              sum collectFirst { case (`ctor`, tpes) if tpes.size == args.size =>
                val (typedArgs, argInfos) = (args zip tpes map { (arg, tpe) =>
                  arg.withExtrinsicInfo(Specified(tpe)).withIntrinsicInfo(Typing.Pattern)
                }).unzip
                if argInfos forall { _.tpe.nonEmpty } then
                  Match(pattern)(ctor, typedArgs) -> Typing(Some(Sum(List(ctor -> (argInfos map { _.tpe.get })))))
                else
                  Match(pattern)(ctor, typedArgs) -> Typing(None)
              }
          }).flatten
          result getOrElse Match(pattern)(ctor, args) -> Typing(None)
        }

      case Bind(ident: Symbol) =>
        pattern -> Typing(pattern.info(Specified) map { _.tpe })
  end Pattern

  object Term extends Enrichment.Intrinsic[Term, Typing]:
    def make(expr: Term) =
      val context = expr.info(Context) getOrElse Context(Map.empty, Set.empty)
      val term = expr.withoutInfo(Context)

      def vars(pattern: Pattern): Map[Symbol, Type] = pattern match
        case Match(_, args: List[Pattern]) => (args flatMap vars).toMap
        case Bind(ident) => pattern.info(Specified) match
          case Some(Specified(tpe)) => Map(ident -> tpe)
          case None => Map.empty

      term match
        case Abs(properties, ident, tpe, expr) =>
          let(tpe.withIntrinsicInfo(Syntactic.Type)) { (tpe, tpeInfo) =>
            if wellDefined(tpe) && (tpeInfo.freeTypeVars subsetOf context.typeVars) then
              let(context.copy(vars = context.vars + (ident -> tpe))) { context =>
                let(expr.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (expr, exprInfo) =>
                  Abs(term)(properties, ident, tpe, expr) -> Typing(exprInfo.tpe map { Function(tpe, _) })
                }
              }
            else
              term -> Typing(None)
          }
        case App(properties, expr, arg) =>
          let(expr.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (expr, exprInfo) =>
            let(arg.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (arg, argInfo) =>
              val unfolded = exprInfo.tpe flatMap {
                case tpe: Recursive => unfold(tpe)
                case tpe => Some(tpe)
              }
              val result = unfolded collect {
                case Function(arg, result) if argInfo.tpe exists { conforms(_, arg) } => result
              }
              App(term)(properties, expr, arg) -> Typing(result)
            }
          }
        case TypeAbs(ident, expr) =>
          let(context.copy(typeVars = context.typeVars + ident)) { context =>
            let(expr.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (expr, exprInfo) =>
              TypeAbs(term)(ident, expr) -> Typing(exprInfo.tpe map { Universal(ident, _) })
            }
          }
        case TypeApp(expr, tpe) =>
          let(expr.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (expr, exprInfo) =>
            val unfolded = exprInfo.tpe flatMap {
              case tpe: Recursive => unfold(tpe)
              case tpe => Some(tpe)
            }
            val result = unfolded collect {
              case Universal(ident, result) => subst(result, Map(ident -> tpe))
            }

            let(tpe.withIntrinsicInfo(Syntactic.Type)) { (tpe, tpeInfo) =>
              if wellDefined(tpe) && (tpeInfo.freeTypeVars subsetOf context.typeVars) then
                TypeApp(term)(expr, tpe) -> Typing(result)
              else
                TypeApp(term)(expr, tpe) -> Typing(None)
            }
          }
        case Data(ctor, args) =>
          let(args.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (args, argsInfos) =>
            val argsTypes = (argsInfos map { _.tpe }).sequenceIfDefined
            Data(term)(ctor, args) -> Typing(argsTypes map { tpes => fold(Sum(List(ctor -> tpes))) })
          }
        case Var(ident) =>
          val tpe = context.vars get ident orElse { term.info(Specified) map { _.tpe } }
          (tpe map { tpe => term.withExtrinsicInfo(Specified(tpe)) } getOrElse term) -> Typing(tpe)
        case Cases(scrutinee, cases) =>
          let(scrutinee.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (scrutinee, scrutineeInfo) =>
            scrutineeInfo.tpe match
              case Some(scrutineeType) =>
                val (typedCases, patternsTypes, exprsTypes) = (cases map { (pattern, expr) =>
                  val (typedPattern, patternInfo) =
                    pattern.withExtrinsicInfo(Specified(scrutineeType)).withIntrinsicInfo(Typing.Pattern)

                  if patternInfo.tpe.nonEmpty then
                    let(context.copy(vars = context.vars ++ vars(typedPattern))) { context =>
                      let(expr.withExtrinsicInfo(context).withIntrinsicInfo(Typing.Term)) { (expr, exprInfo) =>
                        (typedPattern -> expr, patternInfo.tpe, exprInfo.tpe)
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
