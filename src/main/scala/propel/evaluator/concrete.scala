package propel
package evaluator

import ast.*
import util.*

object Concrete:
  def eval(term: Term): Term = term match
    case Abs(_, _, _, _) =>
      term
    case App(properties, expr, arg) =>
      let(eval(arg)) { arg =>
        let(arg.withIntrinsicInfo(Syntactic.Term)) { (arg, argInfo) =>
          eval(expr) match
            case Abs(_, ident, _, expr) if argInfo.closed && argInfo.value =>
              eval(subst(expr, Map(ident -> arg)))
            case expr =>
              App(term)(properties, expr, arg)
        }
      }
    case TypeAbs(_, _) =>
      term
    case TypeApp(expr, tpe) =>
      eval(expr) match
        case TypeAbs(ident, expr) =>
          eval(subst(expr, Map(ident -> tpe)))
        case expr =>
          TypeApp(term)(expr, tpe)
    case Data(ctor, args) =>
      Data(term)(ctor, args map eval)
    case Var(_)=>
      term
    case Cases(scrutinee, cases) =>
      let(eval(scrutinee)) { scrutinee =>
        def process(processingCases: List[(Pattern, Term)]): Term = processingCases match
          case Nil =>
            Cases(term)(scrutinee, cases)
          case (pattern, expr) :: tail =>
            Unification.unify(pattern, scrutinee) match
              case Unification.Full(substs) =>
                val substsInfos = substs.view mapValues { _.withIntrinsicInfo(Syntactic.Term) }
                if substsInfos.values forall { (_, info) => info.closed && info.value } then
                  eval(subst(expr, (substsInfos mapValues { (expr, _) => expr }).toMap))
                else
                  Cases(term)(scrutinee, List(pattern -> expr))

              case Unification.Irrefutable(_, _) =>
                Cases(term)(scrutinee, List(pattern -> expr))

              case _ =>
                process(tail)

        process(cases)
      }
  end eval
end Concrete
