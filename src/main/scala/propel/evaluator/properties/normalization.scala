package propel
package evaluator
package properties

import ast.*
import util.*

case class Normalization(pattern: Term, result: Term, abstraction: Symbol, form: Option[Term], variables: Set[Symbol]):
  private def binds(pattern: Pattern): Set[Symbol] = pattern match
    case Match(ctor, args) => (args flatMap binds).toSet
    case Bind(ident) => Set(ident)

  private def rename(term: Term, mapping: Map[Symbol, Set[Symbol]], bound: Set[Symbol]): (Term, Map[Symbol, Set[Symbol]]) = term match
    case Abs(properties, ident, tpe, expr) =>
      let(rename(expr, mapping, bound + ident)) { Abs(term)(properties, ident, tpe, _) -> _ }
    case App(properties, expr, arg) =>
      let(rename(expr, mapping, bound)) { (expr, mapping) =>
        let(rename(arg, mapping, bound)) { App(term)(properties, expr, _) -> _ }
      }
    case TypeAbs(ident, expr) =>
      let(rename(expr, mapping, bound)) { TypeAbs(term)(ident, _) -> _ }
    case TypeApp(expr, tpe) =>
      let(rename(expr, mapping, bound)) { TypeApp(term)(_, tpe) -> _ }
    case Data(ctor, args) =>
      val renamed = args.foldRight(List.empty[Term], mapping) {
        case (arg, (args, mapping)) =>
          let(rename(arg, mapping, bound)) { (arg, mapping) => (arg :: args) -> mapping }
      }
      let(renamed) { Data(term)(ctor, _) -> _ }
    case Var(ident) =>
      if bound contains ident then
        term -> mapping
      else
        val fresh = Naming.freshIdent(ident, mapping.values.toSet flatMap { _ map { _.name } })
        Var(term)(fresh) -> mapping.updatedWith(ident) { _ map { _ + fresh } orElse Some(Set(fresh)) }
    case Cases(scrutinee, cases) =>
      let(rename(scrutinee, mapping, bound)) { (scrutinee, mapping) =>
        val renamed = cases.foldRight(List.empty[(Pattern, Term)], mapping) {
          case (pattern -> expr, (cases, mapping)) =>
            let(rename(expr, mapping, bound ++ binds(pattern))) { (expr, mapping) => (pattern -> expr :: cases) -> mapping }
        }
        let(renamed) { Cases(term)(scrutinee, _) -> _ }
      }

  val free =
    pattern.syntacticInfo.freeVars.keySet ++
    result.syntacticInfo.freeVars.keySet --
    variables -
    abstraction

  val checking =
    def mappingSubst(mapping: Map[Symbol, Set[Symbol]]) =
      mapping collect { case (original, renamed) if abstraction != original && !(free contains original) =>
        original -> Var(renamed.head)
      }

    def mappingAbstractions(mapping: Map[Symbol, Set[Symbol]]) =
      mapping.getOrElse(abstraction, Set.empty) + abstraction

    def mappingFree(mapping: Map[Symbol, Set[Symbol]]) =
      mapping.foldLeft((free map { free => free -> free}).toMap) { case (result, (original, renamed)) =>
        if free contains original then
          result ++ (renamed map { _ -> original })
        else
          result
      }

    def mappingVariables(mapping: Map[Symbol, Set[Symbol]]) =
      (mapping collect { case (original, renamed) if renamed.size > 1 && (variables contains original) =>
        renamed
      }).toList

    val renamedForm = form map { form =>
      val (renamedForm, formMapping) = rename(form, Map.empty, Set.empty)
      renamedForm.withSyntacticInfo -> mappingVariables(formMapping)
    }

    val (renamedPattern, patternMapping) = rename(pattern, Map.empty, Set.empty)

    val renamedResult = subst(result, mappingSubst(patternMapping))

    Normalization.Checking(
      renamedPattern.withSyntacticInfo,
      renamedResult.withSyntacticInfo,
      mappingAbstractions(patternMapping),
      mappingVariables(patternMapping),
      renamedForm,
      mappingFree(patternMapping))
  end checking
end Normalization

object Normalization:
  case class Checking(
      pattern: Term,
      result: Term,
      abstraction: Set[Symbol],
      equivalents: List[Set[Symbol]],
      form: Option[(Term, List[Set[Symbol]])],
      free: Map[Symbol, Symbol]):
    def apply(expr: Term, checkAbstraction: Set[Term] => Boolean, freeExpr: Map[Symbol, Term]) =
      val freeSubsts = Option.when(free.values forall { freeExpr contains _}) {
        free map { (renamed, original) => renamed -> freeExpr(original) }
      }

      new PropertyChecking with PropertyChecking.FunctionEqualResult with PropertyChecking.Normal:
        def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
          def expandCalls(term: Term): Term = term match
            case Abs(properties, ident, tpe, expr) =>
              Abs(term)(properties, ident, tpe, expandCalls(expr))
            case App(_, App(_, Var(ident), arg0), arg1) if abstraction contains ident =>
              subst(expr, Map(ident0 -> expandCalls(arg0), ident1 -> expandCalls(arg1)))
            case App(properties, expr, arg) =>
              App(term)(properties, expandCalls(expr), expandCalls(arg))
            case TypeAbs(ident, expr) =>
              TypeAbs(term)(ident, expandCalls(expr))
            case TypeApp(expr, tpe) =>
              TypeApp(term)(expandCalls(expr), tpe)
            case Data(ctor, args) =>
              Data(term)(ctor, args map expandCalls)
            case Var(ident) =>
              freeSubsts flatMap { _.get(ident) } getOrElse term
            case Cases(scrutinee, cases) =>
              Cases(term)(expandCalls(scrutinee), cases map { (pattern, expr) =>
                pattern -> expandCalls(expr)
              })
          Data(equalDataConstructor, List(expandCalls(pattern), expandCalls(result))) -> Equalities.empty

        def normalize(equalities: Equalities) = scala.Function.unlift { (term: Term) =>
          def valid(substs: TermSubstitutions, equivalents: List[Set[Symbol]]) =
            equivalents forall { equivalents =>
              (equivalents flatMap { substs get _ }).size == 1
            }

          val (formPattern, formEquivalents) = form match
            case Some(formPattern, formEquivalents) => Some(formPattern) -> formEquivalents
            case _ => None -> List.empty

          freeSubsts flatMap { freeSubsts =>
            Unification.unify(pattern, term) flatMap { (substs, substsReverse) =>
              if substsReverse.isEmpty && checkAbstraction(abstraction flatMap { substs.get(_) }) && valid(substs, equivalents) then
                val formSubsts = formPattern map { formPattern =>
                  abstraction flatMap {
                    substs.get(_) map {
                      Unification.unify(formPattern, _) collect { case (substs, substsReverse) if substsReverse.isEmpty => substs }
                    }
                  }
                }

                if formSubsts.isEmpty || (formSubsts.get.size == 1 && formSubsts.get.head.isDefined) then
                  let(formSubsts map { _.head.get } getOrElse Map.empty) { formSubsts =>
                    Option.when(valid(formSubsts, formEquivalents)) {
                      subst(result, substs ++ formSubsts ++ freeSubsts ++ (abstraction map { _ -> expr }))
                    }
                  }
                else
                  None
              else
                None
            }
          }
        }
    end apply
  end Checking
end Normalization
