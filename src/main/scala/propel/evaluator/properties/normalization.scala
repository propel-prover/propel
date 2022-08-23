package propel
package evaluator
package properties

import ast.*
import util.*

case class Normalization(pattern: Term, result: Term, idents: Set[Symbol], form: Option[Term]):
  def checking(consider: Set[Term] => Boolean, expr: Term) =
    new PropertyChecking with PropertyChecking.FunctionEqualResult with PropertyChecking.Normal:
      def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
        def expandCalls(term: Term): Term = term match
          case Abs(properties, ident, tpe, expr) =>
            Abs(term)(properties, ident, tpe, expandCalls(expr))
          case App(_, App(_, Var(ident), arg0), arg1) if idents contains ident =>
            subst(expr, Map(ident0 -> expandCalls(arg0), ident1 -> expandCalls(arg1)))
          case App(properties, expr, arg) =>
            App(term)(properties, expandCalls(expr), expandCalls(arg))
          case TypeAbs(ident, expr) =>
            TypeAbs(term)(ident, expandCalls(expr))
          case TypeApp(expr, tpe) =>
            TypeApp(term)(expandCalls(expr), tpe)
          case Data(ctor, args) =>
            Data(term)(ctor, args map expandCalls)
          case Var(_) =>
            term
          case Cases(scrutinee, cases) =>
            Cases(term)(expandCalls(scrutinee), cases map { (pattern, expr) =>
              pattern -> expandCalls(expr)
            })
        Data(equalDataConstructor, List(expandCalls(pattern), expandCalls(result))) -> Equalities.empty

      def normalize(equalities: Equalities) = scala.Function.unlift { (term: Term) =>
        Unification.unify(pattern, term) flatMap { (substs, substsReverse) =>
          val formSubsts = form map { form =>
            idents flatMap {
              substs.get(_) map {
                Unification.unify(form, _) collect { case (substs, substsReverse) if substsReverse.isEmpty => substs }
              }
            }
          }

          if formSubsts.isEmpty || (formSubsts.get.size == 1 && formSubsts.get.head.nonEmpty) then
            let(formSubsts map { _.head.get } getOrElse Map.empty) { formSubsts =>
              Option.when(substsReverse.isEmpty && consider(idents flatMap { substs.get(_) })) {
                subst(result, substs ++ formSubsts ++ (idents map { _ -> expr }))
              }
            }
          else
            None
        }
      }
  end checking
end Normalization
