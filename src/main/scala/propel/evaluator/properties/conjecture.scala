package propel
package evaluator
package properties

import ast.*
import typer.*
import util.*

object Conjecture:
  private def freshVarForAbstraction(expr: Term, abstraction: Abstraction, base: String, used: Set[String]): (Term, Set[Symbol]) =
    def freshVarForAbstraction(term: Term, used: Set[String]): (Term, Set[Symbol], Set[String]) =
      if term.info(Abstraction) contains abstraction then
        val name = Naming.freshIdent(base, used)
        val ident = Symbol(name)
        (Var(term)(ident), Set(ident), used + name)
      else
        term match
          case Abs(properties, ident, tpe, expr) =>
            let(freshVarForAbstraction(expr, used)) { (expr, idents, used) =>
              (Abs(term)(properties, ident, tpe, expr), idents, used)
            }
          case App(properties, expr, arg) =>
            let(freshVarForAbstraction(expr, used)) { (expr, identsExpr, used) =>
              let(freshVarForAbstraction(arg, used)) { (arg, identsArg, used) =>
                (App(term)(properties, expr, arg), identsExpr ++ identsArg, used)
              }
            }
          case TypeAbs(ident, expr) =>
            let(freshVarForAbstraction(expr, used)) { (expr, idents, used) =>
              (TypeAbs(term)(ident, expr), idents, used)
            }
          case TypeApp(expr, tpe) =>
            let(freshVarForAbstraction(expr, used)) { (expr, idents, used) =>
              (TypeApp(term)(expr, tpe), idents, used)
            }
          case Data(ctor, args) =>
            val processedArgs = args.foldRight(List.empty[Term], Set.empty[Symbol], used) {
              case (arg, (args, idents, used)) =>
                let(freshVarForAbstraction(arg, used)) { (arg, identsArg, used) =>
                  (arg :: args, idents ++ identsArg, used)
                }
            }
            let(processedArgs) { (args, idents, used) => (Data(term)(ctor, args), idents, used) }
          case Var(_) =>
            (term, Set.empty, used)
          case Cases(scrutinee, cases) =>
            let(freshVarForAbstraction(scrutinee, used)) { (scrutinee, idents, used) =>
              val processedCases = cases.foldRight(List.empty[(Pattern, Term)], Set.empty[Symbol], used) {
                case (pattern -> expr, (cases, idents, used)) =>
                  let(freshVarForAbstraction(expr, used)) { (expr, identsArg, used) =>
                    (pattern -> expr :: cases, idents ++ identsArg, used)
                  }
              }
              let(processedCases) { (cases, idents, used) => (Cases(term)(scrutinee, cases), idents, used) }
            }

    let(freshVarForAbstraction(expr, used)) { (expr, idents, _) => (expr, idents) }
  end freshVarForAbstraction

  private def formToCoverIdents(call: Term, idents: Set[Symbol]): Option[Term] = call match
    case _ if idents.isEmpty =>
      Some(Var(Symbol("∘")))
    case App(properties, expr, Var(ident)) if idents contains ident =>
      formToCoverIdents(expr, idents - ident) map { App(call)(properties, _, Var(ident)) }
    case _ =>
      None

  private def normalizable(normalize: PartialFunction[Term, ?], expr: Term): Boolean =
    (normalize isDefinedAt expr) || {
    expr match
      case Abs(_, _, _, expr) => normalizable(normalize, expr)
      case App(_, expr, arg) => normalizable(normalize, expr) || normalizable(normalize, arg)
      case TypeAbs(ident, expr) => normalizable(normalize, expr)
      case TypeApp(expr, tpe) => normalizable(normalize, expr)
      case Data(_, args) => args exists { normalizable(normalize, _) }
      case Var(_) => false
      case Cases(scrutinee, cases) => normalizable(normalize, scrutinee) || (cases exists { (_, expr) =>
        normalizable(normalize, expr)
      })
    }

  private def recursiveNormalization(lhs: Term, rhs: Term, abstraction: Abstraction, call: Term, names: Set[String]) =
    val data = Data(Constructor(Symbol("⥱")), List(lhs, rhs))
    let(freshVarForAbstraction(data, abstraction, "∘", names)) { update =>
      val (Data(_, List(lhs, rhs)), idents) = update
      val remainingIdents = rhs.syntacticInfo.freeVars.keySet -- lhs.syntacticInfo.freeVars.keySet -- idents
      val form = if remainingIdents.isEmpty then Some(None) else formToCoverIdents(call, remainingIdents) map { Some(_) }
      lhs -> (form flatMap { form => validateNormalization(Normalization(lhs, rhs, idents, form), abstraction, Some(call)) })
    }

  private def directNormalization(properties: Properties, arg0: Term, arg1: Term, rhs: Term, abstraction: Abstraction, names: Set[String]) =
    val ident = Naming.freshIdent(Symbol("∘"), names)
    val lhs = App(Set.empty, App(properties, Var(ident), arg0), arg1)
    val form = Option.when(rhs.syntacticInfo.freeVars.keySet - ident subsetOf lhs.syntacticInfo.freeVars.keySet)(None)
    lhs -> (form flatMap { form => validateNormalization(Normalization(lhs, rhs, Set(ident), form), abstraction, None) })

  private def validateNormalization(normalization: Normalization, abstraction: Abstraction, call: Option[Term]) =
    val checking = normalization.checking(
      _ forall { _.info(Abstraction) contains abstraction },
      call getOrElse Data(Constructor(Symbol("∅")), List.empty))
    val normalize = checking.normalize(Equalities.empty)
    Option.when(!normalizable(normalize, normalization.result))(normalization)

  def basicFacts(
      properties: Properties,
      abstraction: Term,
      ident0: Symbol,
      ident1: Symbol,
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    (abstraction.info(Abstraction), recursiveCall(abstraction)) match
      case (Some(abstraction), call) =>
        result unwrap { result =>
          val names = UniqueNames.usedNames.toSet

          val (_, normalizations) = result.reductions.foldLeft(List.empty[Term], List.empty[Normalization]) {
            case ((patterns, normalizations), Symbolic.Reduction(expr, _, equalities)) =>
              val freeVars = expr.syntacticInfo.freeVars.keySet

              val var0 = Var(ident0)
              val var1 = Var(ident1)

              val arg0 = Option.when(freeVars contains ident0)(var0) orElse equalities.pos.get(var0) getOrElse var0
              val arg1 = Option.when(freeVars contains ident1)(var1) orElse equalities.pos.get(var1) getOrElse var1

              val lhs -> normalization = call match
                case Some(call) =>
                  recursiveNormalization(App(Set.empty, App(properties, call, arg0), arg1), expr, abstraction, call, names)
                case _ =>
                  directNormalization(properties, arg0, arg1, expr, abstraction, names)

              (lhs :: patterns) -> (normalization match {
                case Some(normalization) if patterns forall { Unification.refutable(normalization.pattern, _) } =>
                  normalization :: normalizations
                case _ =>
                  normalizations
              })
          }

          normalizations sortBy {
            case Normalization(pattern, result, _, _) => (pattern, result)
          }
        }
      case _ =>
        List.empty
  end basicFacts

  def generalizedConjectures(
      properties: Properties,
      abstraction: Term,
      ident0: Symbol,
      ident1: Symbol,
      tpe: Type,
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    def injectRecursiveCallBasedOnType(term: Term, call: Term, argument: Either[Term, Term]): List[Term] =
      val result = term match
        case Abs(properties, ident, tpe, expr) =>
          injectRecursiveCallBasedOnType(expr, call, argument) collect { Abs(term)(properties, ident, tpe, _) }
        case App(properties, expr, arg) =>
          (injectRecursiveCallBasedOnType(expr, call, argument) collect { App(term)(properties, _, arg) }) ++
          (injectRecursiveCallBasedOnType(arg, call, argument) collect { App(term)(properties, expr, _)  })
        case TypeAbs(ident, expr) =>
          injectRecursiveCallBasedOnType(expr, call, argument) collect { TypeAbs(ident, _) }
        case TypeApp(expr, tpe) =>
          injectRecursiveCallBasedOnType(expr, call, argument) collect { TypeApp(_, tpe) }
        case Data(ctor, args) =>
          def process(args: List[Term]): List[List[Term]] = args match
            case arg :: args =>
              (injectRecursiveCallBasedOnType(arg, call, argument) collect { _ :: args }) ++
              (process(args) map { arg :: _ })
            case _ =>
              List.empty
          process(args) map { Data(term)(ctor, _) }
        case Var(_) =>
          List.empty
        case Cases(scrutinee, cases) =>
          def process(cases: List[(Pattern, Term)]): List[List[(Pattern, Term)]] = cases match
            case (patternExpr @ (pattern -> expr)) :: cases =>
              (injectRecursiveCallBasedOnType(expr, call, argument) collect { pattern -> _ :: cases }) ++
              (process(cases) map { patternExpr :: _ })
            case _ =>
              List.empty
          (injectRecursiveCallBasedOnType(scrutinee, call, argument) collect { Cases(term)(_, cases) }) ++
          (process(cases) map { Cases(term)(scrutinee, _) })

      if term.termType exists { conforms(_, tpe) } then
        argument match
          case Left(argument) => App(Set.empty, App(properties, call, argument), term) :: result
          case Right(argument) => App(Set.empty, App(properties, call, term), argument) :: result
      else
        result
    end injectRecursiveCallBasedOnType

    def containsReference(expr: Term, abstraction: Abstraction): Boolean = expr match
      case Abs(_, _, _, expr) => containsReference(expr, abstraction)
      case App(_, expr, arg) => containsReference(expr, abstraction) || containsReference(arg, abstraction)
      case TypeAbs(ident, expr) => containsReference(expr, abstraction)
      case TypeApp(expr, tpe) => containsReference(expr, abstraction)
      case Data(_, args) => args exists { containsReference(_, abstraction) }
      case Var(_) => expr.info(Abstraction) contains abstraction
      case Cases(scrutinee, cases) => containsReference(scrutinee, abstraction) || (cases exists { (_, expr) =>
        containsReference(expr, abstraction)
      })

    def generalizeEvaluationResults(ident0: Symbol, ident1: Symbol, abstraction: Abstraction, call: Term) =
      result unwrap { result =>
        val names = UniqueNames.usedNames.toSet

        val (patternName0, patternName1) = let(Naming.dropSubscript(ident0.name), Naming.dropSubscript(ident1.name)) { case names @ (name0, name1) =>
          if name0 != name1 then names
          else if name0.length == 1 then
            val c = name0.head.toInt
            if c >= '0' && c <= '8' then name0 -> (c + 1).toChar.toString
            else if c == '9' then name0 -> "8"
            else if c >= 'A' && c <= 'Y' then name0 -> (c + 1).toChar.toString
            else if c == 'Z' then name0 -> "Y"
            else if c >= 'a' && c <= 'y' then name0 -> (c + 1).toChar.toString
            else if c == 'z' then name0 -> "y"
            else s"$name0:a" -> s"$name0:b"
          else s"$name0:a" -> s"$name0:b"
        }

        val var0 = Var(if ident0.name == ident1.name then Naming.freshIdent(ident0, names) else ident0)
        val var1 = Var(ident1)

        val normalizedType = normalize(tpe)

        val patterns0 = normalizedType map { patternsByType(_, patternName0, names) map { _.withSyntacticInfo } } getOrElse List.empty
        val patterns1 = normalizedType map { patternsByType(_, patternName1, names) map { _.withSyntacticInfo } } getOrElse List.empty

        patterns0 flatMap { pattern0 =>
          patterns1 flatMap { pattern1 =>
            let(names ++ (pattern0.syntacticInfo.boundVars ++ pattern1.syntacticInfo.boundVars map { _.name })) { names =>
              PatternConstraints.make(List(var0 -> pattern0, var1 -> pattern1)).toList flatMap { constraints =>
                result.withConstraints(constraints).reductions flatMap { case Symbolic.Reduction(expr, _, equalities) =>
                  val arg0 = equalities.pos.getOrElse(var0, var0)
                  val arg1 = equalities.pos.getOrElse(var1, var1)

                  val lhs = App(Set.empty, App(properties, call, arg0), arg1)
                  val rhs = expr

                  val generalizations =
                    val freeVars = rhs.syntacticInfo.freeVars.keys

                    val var0dependents = (equalities.pos.get(var0).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var0.ident
                    val exprDependsOnVar0 = freeVars exists { var0dependents contains _ }

                    val var1dependents = (equalities.pos.get(var1).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var1.ident
                    val exprDependsOnVar1 = freeVars exists { var1dependents contains _ }

                    val lhsVar0 = App(Set.empty, App(properties, call, var0), arg1)
                    val lhsVar1 = App(Set.empty, App(properties, call, arg0), var1)

                    val generalizedVar0 = Option.when(rhs == arg1)(lhsVar0 -> var0)
                    val generalizedVar1 = Option.when(rhs == arg0)(lhsVar1 -> var1)

                    val generalizedRecursiveCalls =
                      if ident0.name != ident1.name && !containsReference(rhs, abstraction) then
                        if !exprDependsOnVar0 && exprDependsOnVar1 then
                          injectRecursiveCallBasedOnType(rhs.typedTerm, call, Left(var0)) collect {
                            case rhs if equalities.equal(rhs, lhsVar0) != Equality.Equal => lhsVar0 -> rhs
                          }
                        else if exprDependsOnVar0 && !exprDependsOnVar1 then
                          injectRecursiveCallBasedOnType(rhs.typedTerm, call, Right(var1)) collect {
                            case rhs if equalities.equal(rhs, lhsVar1) != Equality.Equal => lhsVar1 -> rhs
                          }
                        else
                          List.empty
                      else
                        List.empty

                    generalizedVar0.toList ++ generalizedVar1.toList ++ generalizedRecursiveCalls
                  end generalizations

                  (lhs -> rhs) :: generalizations flatMap { (lhs, rhs) =>
                    val _ -> normalization = recursiveNormalization(lhs, rhs, abstraction, call, names)
                    normalization
                  }
                }
              }
            }
          }
        }
      }

    (abstraction.info(Abstraction), recursiveCall(abstraction)) match
      case (Some(abstraction), Some(call)) =>
        generalizeEvaluationResults(ident0, ident1, abstraction, call).distinct sortBy {
          case Normalization(pattern, result, _, _) => (pattern, result)
        }
      case _ =>
        List.empty
  end generalizedConjectures
end Conjecture
