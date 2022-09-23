package propel
package evaluator
package properties

import ast.*
import typer.*
import util.*

object Conjecture:
  private def replaceAbstraction(term: Term, from: Abstraction, to: Term): Term =
    if term.info(Abstraction) contains from then
      to
    else
      term match
        case Abs(properties, ident, tpe, expr) =>
          Abs(term)(properties, ident, tpe, replaceAbstraction(expr, from, to))
        case App(properties, expr, arg) =>
          App(term)(properties, replaceAbstraction(expr, from, to), replaceAbstraction(arg, from, to))
        case TypeAbs(ident, expr) =>
          TypeAbs(term)(ident, replaceAbstraction(expr, from, to))
        case TypeApp(expr, tpe) =>
          TypeApp(term)(replaceAbstraction(expr, from, to), tpe)
        case Data(ctor, args) =>
          Data(term)(ctor, args map { replaceAbstraction(_, from, to) })
        case Var(_) =>
          term
        case Cases(scrutinee, cases) =>
          Cases(term)(replaceAbstraction(scrutinee, from, to), cases map { _ -> replaceAbstraction(_, from, to) })

  private def formToCoverIdents(call: Term, idents: Set[Symbol]): (Term, Set[Symbol]) = call match
    case App(properties, expr, arg @ Var(ident)) if idents contains ident =>
      let(formToCoverIdents(expr, idents - ident)) { App(call)(properties, _, arg) -> _ }
    case _ =>
      Var(Symbol("∘")) -> idents

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

  private def recursiveNormalization(
      lhs: Term,
      rhs: Term,
      abstraction: Abstraction,
      calls: List[Term],
      unbound: Set[Symbol],
      names: Set[String]) =
    val ident = Naming.freshIdent(Symbol("∘"), names)
    val variable = Var(ident)
    let(replaceAbstraction(lhs, abstraction, variable)) { lhs =>
      let(replaceAbstraction(rhs, abstraction, variable)) { rhs =>
        createNormalization(lhs, rhs, ident, abstraction, calls, unbound, names)
      }
    }

  private def directNormalization(
      properties: Properties,
      arg0: Term,
      arg1: Term, rhs: Term,
      abstraction: Abstraction,
      unbound: Set[Symbol],
      names: Set[String]) =
    val ident = Naming.freshIdent(Symbol("∘"), names)
    val lhs = App(Set.empty, App(properties, Var(ident), arg0), arg1)
    createNormalization(lhs, rhs, ident, abstraction, List.empty, unbound, names)

  private def createNormalization(
      lhs: Term,
      rhs: Term,
      ident: Symbol,
      abstraction: Abstraction,
      calls: List[Term],
      unbound: Set[Symbol],
      names: Set[String]) =
    let(rhs.syntactic) { (rhs, rhsInfo) =>
      let(lhs.syntactic) { (lhs, lhsInfo) =>
        val remaining = rhsInfo.freeVars.keySet -- lhsInfo.freeVars.keySet - ident
        if remaining forall { unbound contains _ } then
          val forms = calls map { formToCoverIdents(_, remaining) }
          val form = forms.toSet.toList match
            case List(Var(_) -> remaining) => None -> remaining
            case List(form -> remaining) => Some(form) -> remaining
            case _ => None -> remaining

          let(form) { (form, remaining) =>
            def dummy = Data(Constructor(Symbol("∅")), List.empty)
            val variables = rhsInfo.freeVars.keySet ++ lhsInfo.freeVars.keySet -- unbound - ident
            val normalization = Normalization(lhs, rhs, ident, form, variables)
            val checking = normalization.checking(
              calls.headOption getOrElse dummy,
              _ forall { _.info(Abstraction) contains abstraction },
              (normalization.free map { ident => ident -> Var(ident) }).toMap)
            val normalize = checking.normalize(Equalities.empty)
            lhs -> Option.when(!normalizable(normalize, normalization.checking.result))(normalization)
          }
        else
          lhs -> None
      }
    }
  end createNormalization

  def basicFacts(
      properties: Properties,
      abstraction: Term,
      ident0: Symbol,
      ident1: Symbol,
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    val unbound = abstraction.syntacticInfo.freeVars.keySet

    (abstraction.info(Abstraction), recursiveCalls(abstraction)) match
      case (Some(abstraction), calls) =>
        val call = calls.headOption

        result unwrap { result =>
          val names = UniqueNames.usedNames.toSet

          val (_, normalizations) = result.reductions.foldLeft(List.empty[Term], List.empty[Normalization]) {
            case ((patterns, normalizations), Symbolic.Reduction(expr, _, equalities)) =>
              let(expr.syntactic) { (expr, exprInfo) =>
                val freeVars = exprInfo.freeVars.keySet

                val var0 = Var(ident0)
                val var1 = Var(ident1)

                val arg0 = Option.when(freeVars contains ident0)(var0) orElse equalities.pos.get(var0) getOrElse var0
                val arg1 = Option.when(freeVars contains ident1)(var1) orElse equalities.pos.get(var1) getOrElse var1

                val lhs -> normalization = call match
                  case Some(call) =>
                    recursiveNormalization(App(Set.empty, App(properties, call, arg0), arg1), expr, abstraction, calls, unbound, names)
                  case _ =>
                    directNormalization(properties, arg0, arg1, expr, abstraction, unbound, names)

                (lhs :: patterns) -> (normalization match {
                  case Some(normalization)
                      if (patterns forall { Unification.refutable(normalization.checking.pattern, _) }) &&
                         (var0 != arg0 || var1 != arg1) =>
                    normalization :: normalizations
                  case _ =>
                    normalizations
                })
              }
          }

          Normalization.distinct(normalizations) sortBy {
            case Normalization(pattern, result, _, _, _) => (pattern, result)
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
    val unbound = abstraction.syntacticInfo.freeVars.keySet

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

    def generalizeEvaluationResults(ident0: Symbol, ident1: Symbol, abstraction: Abstraction, calls: List[Term]) =
      val call = calls.head

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
                  val (rhs, rhsInfo) = expr.syntactic

                  val generalizations =
                    val freeVars = rhsInfo.freeVars.keys

                    val var0dependents = (equalities.pos.get(var0).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var0.ident
                    val exprDependsOnVar0 = freeVars exists { var0dependents contains _ }

                    val var1dependents = (equalities.pos.get(var1).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var1.ident
                    val exprDependsOnVar1 = freeVars exists { var1dependents contains _ }

                    val lhsVar0 = App(Set.empty, App(properties, call, var0), arg1)
                    val lhsVar1 = App(Set.empty, App(properties, call, arg0), var1)
                    val lhsVar01 = App(Set.empty, App(properties, call, var0), var1)

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

                    def swap(term: Term): Term = term match
                      case Abs(properties, ident, tpe, expr) =>
                        Abs(term)(properties, ident, tpe, swap(expr))
                      case App(properties1, expr1 @ App(properties0, expr0, arg0), arg1) if expr0.info(Abstraction) contains abstraction =>
                        App(term)(properties1, App(expr1)(properties0, swap(expr0), swap(arg1)), swap(arg0))
                      case App(properties, expr, arg) =>
                        App(term)(properties, swap(expr), swap(arg))
                      case TypeAbs(ident, expr) =>
                        TypeAbs(term)(ident, swap(expr))
                      case TypeApp(expr, tpe) =>
                        TypeApp(term)(swap(expr), tpe)
                      case Data(ctor, args) =>
                        Data(term)(ctor, args map swap)
                      case Var(ident) =>
                        term
                      case Cases(scrutinee, cases) =>
                        Cases(term)(scrutinee, cases map { (pattern, expr) => pattern -> swap(expr )})

                    ((lhs -> rhs) :: generalizedVar0.toList ++ generalizedVar1.toList ++ generalizedRecursiveCalls
                      flatMap { case generalization @ (_, rhs) =>
                        val freeVars = rhs.syntacticInfo.freeVars.keys

                        val var0dependents = (equalities.pos.get(var0).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var0.ident
                        val exprDependsOnVar0 = freeVars exists { var0dependents contains _ }

                        val var1dependents = (equalities.pos.get(var1).toSet flatMap { _.syntacticInfo.freeVars.keys }) + var1.ident
                        val exprDependsOnVar1 = freeVars exists { var1dependents contains _ }

                        if !exprDependsOnVar0 && !exprDependsOnVar1 then
                          List(generalization, lhsVar0 -> rhs, lhsVar1 -> rhs, lhsVar01 -> rhs)
                        else
                          List(generalization)
                      }
                      flatMap { case generalization @ (lhs, rhs) =>
                        List(generalization, swap(lhs) -> swap(rhs))
                      })
                  end generalizations

                  generalizations flatMap { (lhs, rhs) =>
                    val _ -> normalization = recursiveNormalization(lhs, rhs, abstraction, calls, unbound, names)
                    normalization
                  }
                }
              }
            }
          }
        }
      }

    (abstraction.info(Abstraction), recursiveCalls(abstraction)) match
      case (Some(abstraction), calls @ _ :: _) =>
        Normalization.distinct(generalizeEvaluationResults(ident0, ident1, abstraction, calls)) sortBy {
          case Normalization(pattern, result, _, _, _) => (pattern, result)
        }
      case _ =>
        List.empty
  end generalizedConjectures
end Conjecture
