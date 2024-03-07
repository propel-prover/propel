package propel
package evaluator

import ast.*
import util.*

object Concrete:
  extension (expr: Term)
    private def withStuckTermError = expr.withExtrinsicInfo(Error(
      "Reduction Error\n\nStuck term encountered."))
    private def withUnsubstitutedVarError = expr.withExtrinsicInfo(Error(
      "Reduction Error\n\nUnsubstituted variable encountered."))

  def eval(term: Term): Term = term match
    case Abs(_, _, _, _) =>
      term
    case App(_, App(_, Var(Symbol("prop-for")), _), _)
        if term.info(properties.CustomProperties).isDefined =>
      Data(Constructor(Symbol("Unit")), List.empty)
    case App(properties, expr, arg) =>
      let(eval(arg)) { arg =>
        let(arg.syntactic) { (arg, argInfo) =>
          eval(expr) match
            case Abs(_, ident, _, expr) if argInfo.closed && argInfo.value =>
              eval(subst(expr, Map(ident -> arg)))
            case expr =>
              App(term)(properties, expr, arg).withStuckTermError
        }
      }
    case TypeAbs(_, _) =>
      term
    case TypeApp(expr, tpe) =>
      eval(expr) match
        case TypeAbs(ident, expr) =>
          eval(subst(expr, Map(ident -> tpe)))
        case expr =>
          TypeApp(term)(expr, tpe).withStuckTermError
    case Data(ctor, args) =>
      Data(term)(ctor, args map eval)
    case Var(_)=>
      term.withUnsubstitutedVarError
    case Cases(scrutinee, cases) =>
      let(eval(scrutinee)) { scrutinee =>
        def process(processingCases: List[(Pattern, Term)]): Term = processingCases match
          case Nil =>
            Cases(term)(scrutinee, cases).withStuckTermError
          case (pattern, expr) :: tail =>
            Unification.unify(pattern, scrutinee) match
              case Unification.Full(substs) =>
                val substsInfos = substs.view mapValues { _.syntactic }
                if substsInfos.values forall { (_, info) => info.closed && info.value } then
                  eval(subst(expr, (substsInfos mapValues { (expr, _) => expr }).toMap))
                else
                  Cases(term)(scrutinee, List(pattern -> expr))

              case Unification.Irrefutable(_, _) =>
                Cases(term)(scrutinee, List(pattern -> expr)).withStuckTermError

              case _ =>
                process(tail)

        process(cases)
      }
  end eval
end Concrete
