package propel
package typer

import ast.*
import printing.*
import util.*


extension (expr: Term)
  inline def typed: (Term, Option[Type]) =
    let(expr.withIntrinsicInfo(Typing.Term)) { case expr -> Typing(tpe) => expr -> tpe }
  inline def termType: Option[Type] =
    let(expr.withIntrinsicInfo(Typing.Term)) { case _ -> Typing(tpe) => tpe }
  inline def typedTerm: Term =
    let(expr.withIntrinsicInfo(Typing.Term)) { case expr -> _ => expr }
  inline def untyped: Term =
    Typing.Term.strip(expr)


extension (pattern: Pattern)
  inline def typed: (Pattern, Option[Type]) =
    let(pattern.withIntrinsicInfo(Typing.Pattern)) { case pattern -> Typing(tpe) => pattern -> tpe }
  inline def patternType: Option[Type] =
    let(pattern.withIntrinsicInfo(Typing.Pattern)) { case _ -> Typing(tpe) => tpe }
  inline def typedPattern: Pattern =
    let(pattern.withIntrinsicInfo(Typing.Pattern)) { case pattern -> _ => pattern }
  inline def untyped: Pattern =
    Typing.Pattern.strip(pattern)


case class Typing(tpe: Option[Type]) extends Enrichment(Typing)

object Typing extends Enrichment.Intrinsic[Pattern | Term, Typing]:
  private case class Context(vars: Map[Symbol, Type], typeVars: Set[Symbol], expected: Option[Type]) extends Enrichment(Context)

  private object Context extends Enrichment.Extrinsic[Term, Context]


  case class Specified(tpe: Either[Set[Symbol], Type]) extends Enrichment(Specified)

  object Specified extends Enrichment.Extrinsic[Pattern | Term, Specified]


  extension (pattern: Pattern)
    private def withFruitlessPatternError(tpe: Type) = pattern.withExtrinsicInfo(Error(
      s"Type Error\n\nFruitless pattern ${pattern.show} for type ${tpe.show}."))
    private def withUnkownTypeError = pattern.withExtrinsicInfo(Error(
      s"Type Error\n\nType not known for pattern ${pattern.show}."))

  extension (expr: Term)
    private def withIllformedTypeError(tpe: Type) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nIll-formed type: ${tpe.show}\n\nThis may be caused by conflicting sum type elements."))
    private def withIlltypedApplication(abs: Type, arg: Type) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nValue of type ${arg.show} cannot be applied to value of type ${abs.show}."))
    private def withIlltypedTypeApplication(typeAbs: Type, arg: Type) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nType ${arg.show} cannot be applied to type ${typeAbs.show}."))
    private def withUnboundVarError(variable: Symbol) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nUnbound variable: ${variable.name}"))
    private def withUnboundTypeVarsError(typeVars: Set[Symbol]) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nUnbound type variables${
        if typeVars.isEmpty then "." else s": ${(typeVars map { _.name }).mkString(", ")}"
      }"))
    private def withUnjoinableTypesError(tpes: List[Type]) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nTypes of branches cannot be joined${
        if tpes.isEmpty then "." else s":\n${(tpes map { tpe => s"  • ${tpe.show}" }).mkString("\n")}"
      }"))
    private def withNonexhaustiveCasesError(patterns: List[Pattern]) = expr.withExtrinsicInfo(Error(
      s"Type Error\n\nNon-exhaustive case distinction.${
        if patterns.isEmpty then "" else s"\n\nThe following cases are not covered:\n${(patterns map { pattern => s"  • ${pattern.show}" }).mkString("\n")}"
      }"))


  def strip(construct: Pattern | Term) = construct match
    case construct: Pattern => Pattern.strip(construct)
    case construct: Term => Term.strip(construct)

  def make(construct: Pattern | Term) = construct match
    case construct: Pattern => Pattern.make(construct)
    case construct: Term => Term.make(construct)

  object Pattern extends Enrichment.Intrinsic[Pattern, Typing]:
    def strip(pattern: Pattern): Pattern = pattern.withoutInfo(Typing, Specified, Context) match
      case pattern @ Match(ctor, args) => Match(pattern)(ctor, args map strip)
      case pattern @ Bind(_) => pattern

    def make(pattern: Pattern) =
      val tpe = pattern.info(Specified) flatMap { _.tpe.toOption }
      pattern match
        case Match(ctor, args) =>
          val unfolded = tpe flatMap {
            case tpe: Recursive => unfold(tpe)
            case tpe => Some(tpe)
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

          result getOrElse {
            if tpe.nonEmpty then
              Match(pattern)(ctor, args).withFruitlessPatternError(tpe.get) -> Typing(None)
            else
              Match(pattern)(ctor, args).withUnkownTypeError -> Typing(None)
          }

        case Bind(ident) =>
          if tpe.nonEmpty then
            pattern -> Typing(tpe)
          else
            pattern.withUnkownTypeError -> Typing(None)
  end Pattern

  object Term extends Enrichment.Intrinsic[Term, Typing]:
    def strip(expr: Term): Term = expr.withoutInfo(Typing, Specified, Context, Abstraction) match
      case term @ Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe, strip(expr))
      case term @ App(properties, expr, arg) => App(term)(properties, strip(expr), strip(arg))
      case term @ TypeAbs(ident, expr) => TypeAbs(term)(ident, strip(expr))
      case term @ TypeApp(expr, tpe) => TypeApp(term)(strip(expr), tpe)
      case term @ Data(ctor, args) => Data(term)(ctor, args map strip)
      case term @ Var(_) => term
      case term @ Cases(scrutinee, cases) => Cases(term)(strip(scrutinee), cases map { (pattern, expr) =>
        Pattern.strip(pattern) -> strip(expr)
      })

    def make(expr: Term) =
      val context = expr.info(Context) getOrElse Context(Map.empty, Set.empty, Option.empty)
      val term = expr.withoutInfo(Context)

      def vars(pattern: Pattern): Map[Symbol, Type] = pattern match
        case Match(_, args) => (args flatMap vars).toMap
        case Bind(ident) => pattern.info(Specified) match
          case Some(Specified(Right(tpe))) => Map(ident -> tpe)
          case _ => Map.empty

      val (resultExpr, resultTyping) = term match
        case Abs(properties, ident, tpe, expr) =>
          val (expectedType, expectedArgType, expectedResultType) = context.expected match
            case Some(expected @ Function(arg, result)) => (Some(expected), Some(arg), Some(result))
            case _ => (None, None, None)

          let(Abstraction.assign(expectedArgType, tpe).syntactic) { (tpe, tpeSyntactic) =>
            let(context.copy(vars = context.vars + (ident -> tpe), expected = expectedResultType)) { context =>
              let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
                val typeVars = term.info(Specified) match
                  case Some(Specified(Left(tpe))) => context.typeVars ++ tpe
                  case _ => context.typeVars

                val unboundTypeVars = tpeSyntactic.freeTypeVars -- typeVars
                val abs = Abs(term)(properties, ident, tpe, expr).withExtrinsicInfo(Specified(Left(typeVars)))

                if !wellFormed(tpe) then
                  abs.withIllformedTypeError(tpe) -> Typing(None)
                else if unboundTypeVars.nonEmpty then
                  abs.withUnboundTypeVarsError(unboundTypeVars) -> Typing(None)
                else
                  abs -> Typing(exprType map { exprType =>
                    Abstraction.assign(expectedType, Function(tpe, exprType))
                  })
              }
            }
          }

        case App(properties, expr, arg) =>
          let(expr.withExtrinsicInfo(context.copy(expected = None)).typed) { (expr, exprType) =>
            val expectedArgType = exprType collect { case Function(arg, _) => arg }

            let(arg.withExtrinsicInfo(context.copy(expected = expectedArgType)).typed) { (arg, argType) =>
              val unfolded = exprType flatMap {
                case tpe: Recursive => unfold(tpe)
                case tpe => Some(tpe)
              }
              val result = unfolded collect {
                case Function(arg, result) if argType exists { conforms(_, arg) } => result
              }

              val app = App(term)(properties, expr, arg)

              if result.isEmpty && exprType.nonEmpty && argType.nonEmpty then
                app.withIlltypedApplication(exprType.get, argType.get) -> Typing(result)
              else
                app -> Typing(result)
            }
          }

        case TypeAbs(ident, expr) =>
          val (expectedType, expectedResultType) = context.expected match
            case Some(expected @ Universal(_, result)) => (Some(expected), Some(result))
            case _ => (None, None)

          let(context.copy(typeVars = context.typeVars + ident, expected = expectedResultType)) { context =>
            let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
              TypeAbs(term)(ident, expr) -> Typing(exprType map { exprType =>
                Abstraction.assign(expectedType, Universal(ident, exprType))
              })
            }
          }

        case TypeApp(expr, tpe) =>
          let(expr.withExtrinsicInfo(context.copy(expected = None)).typed) { (expr, exprType) =>
            let(Abstraction.assign(tpe).syntactic) { (tpe, tpeSyntactic) =>
              val typeVars = term.info(Specified) match
                case Some(Specified(Left(tpe))) => context.typeVars ++ tpe
                case _ => context.typeVars

              val unfolded = exprType flatMap {
                case tpe: Recursive => unfold(tpe)
                case tpe => Some(tpe)
              }
              val result = unfolded collect {
                case Universal(ident, result) => subst(result, Map(ident -> tpe))
              }

              val unboundTypeVars = tpeSyntactic.freeTypeVars -- typeVars
              val typeApp = TypeApp(term)(expr, tpe).withExtrinsicInfo(Specified(Left(typeVars)))

              if !wellFormed(tpe) then
                typeApp.withIllformedTypeError(tpe) -> Typing(None)
              else if unboundTypeVars.nonEmpty then
                typeApp.withUnboundTypeVarsError(unboundTypeVars) -> Typing(None)
              else if result.isEmpty && exprType.nonEmpty then
                typeApp.withIlltypedTypeApplication(exprType.get, tpe) -> Typing(result)
              else
                typeApp -> Typing(result)
            }
          }

        case Data(ctor, args) =>
          val expectedArgTypes = (context.expected collect { case Sum(sum) =>
            sum collectFirst { case `ctor` -> argsTypes if argsTypes.size == args.size => argsTypes map { Some(_) } }
          }).flatten

          val typedArgs = expectedArgTypes getOrElse List.fill(args.size)(None) zip args map { (expectedArgType, arg) =>
            arg.withExtrinsicInfo(context.copy(expected = expectedArgType)).typed
          }

          let(typedArgs.unzip) { (args, argsInfos) =>
            val argsTypes = argsInfos.sequenceIfDefined
            Data(term)(ctor, args) -> Typing(argsTypes map { tpes => fold(Sum(List(ctor -> tpes))) })
          }

        case Var(ident) =>
          val tpe = context.vars get ident orElse { term.info(Specified) collect { case Specified(Right(tpe)) => tpe } }
          tpe match
            case some @ Some(tpe) => term.withExtrinsicInfo(Specified(Right(tpe))) -> Typing(some)
            case _ => term.withUnboundVarError(ident) -> Typing(None)

        case Cases(scrutinee, cases) =>
          let(scrutinee.withExtrinsicInfo(context).typed) { (scrutinee, scrutineeType) =>
            scrutineeType match
              case Some(scrutineeType) =>
                val (typedCases, exprsTypes) = (cases map { (pattern, expr) =>
                  val (typedPattern, patternType) =
                    pattern.withExtrinsicInfo(Specified(Right(scrutineeType))).typed

                  if patternType.nonEmpty then
                    let(context.copy(vars = context.vars ++ vars(typedPattern))) { context =>
                      let(expr.withExtrinsicInfo(context).typed) { (expr, exprType) =>
                        typedPattern -> expr -> exprType
                      }
                    }
                  else
                    typedPattern -> expr -> None
                }).unzip

                val (casePatterns, _) = cases.unzip

                let(exprsTypes.sequenceIfDefined) { exprsTypes =>
                  val cases = Cases(term)(scrutinee, typedCases)

                  casePatterns.foldLeft(scrutineeType) { (tpe, pattern) => diff(tpe, pattern) getOrElse tpe } match
                    case Sum(List()) => exprsTypes match
                      case Some(exprsTypes) => exprsTypes reduceLeftIfDefined { join(_, _) } match
                        case exprType @ Some(_) => cases -> Typing(exprType)
                        case _ => cases.withUnjoinableTypesError(exprsTypes) -> Typing(None)
                      case _ => cases -> Typing(None)
                    case tpe => cases.withNonexhaustiveCasesError(patterns(tpe)) -> Typing(None)
                }

              case _ =>
                Cases(term)(scrutinee, cases) -> Typing(None)
          }

      (resultTyping.tpe flatMap { _.info(Abstraction) map { resultExpr.withExtrinsicInfo(_) } } getOrElse resultExpr) -> resultTyping
  end Term
end Typing
