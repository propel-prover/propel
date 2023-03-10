package propel
package evaluator
package properties

import ast.*
import typer.*

case class DecreasingArguments(first: Boolean, second: Boolean, combined: Boolean)

object DecreasingArguments:
  def check(term: Term, names: Iterable[String] = Iterable.empty): Option[DecreasingArguments] =
    term.typedTerm match
      case term @ Abs(_, ident0, _, Abs(_, ident1, _, expr)) =>
        val (found, first, second, combined) = term.info(Abstraction).fold(false, true, true, true) { abstraction =>
          Symbolic.eval(UniqueNames.convert(expr, names)).wrapped.reductions.foldLeft(false, true, true, true) {
            case (result @ (found, false, false, false), _) =>
              result
            case (result, Symbolic.Reduction(expr, Symbolic.Constraints(pos, _), equalities)) =>
              (pos.keys ++ List(expr) flatMap { recursiveArguments(_, abstraction) }).foldLeft(result) {
                case (result @ (found, false, false, false), _) =>
                  result
                case ((found, first, second, combined), (arg0, arg1)) =>
                  val var0 = Var(ident0)
                  val expr0Weight = Weight(equalities.pos.get(var0) getOrElse var0)
                  val var1 = Var(ident1)
                  val expr1Weight = Weight(equalities.pos.get(var1) getOrElse var1)

                  val arg0Weight = Weight(arg0)
                  val arg1Weight = arg1 map { Weight(_) }

                  (true,
                   first && arg0Weight < expr0Weight,
                   second && arg1Weight.isDefined && arg1Weight.get < expr1Weight,
                   combined && arg1Weight.isDefined && arg0Weight + arg1Weight.get < expr0Weight + expr1Weight)
                }
          }
        }
        Option.when(found)(DecreasingArguments(first, second, combined))
      case _ =>
        None
  end check

  private def recursiveArguments(term: Term, abstraction: Abstraction): List[(Term, Option[Term])] = term match
    case Abs(properties, ident, tpe, expr) =>
      recursiveArguments(expr, abstraction)
    case App(_, App(_, expr, arg0), arg1) if expr.info(Abstraction) contains abstraction =>
      (arg0, Some(arg1)) ::
      recursiveArguments(expr, abstraction) ++
      recursiveArguments(arg0, abstraction) ++
      recursiveArguments(arg1, abstraction)
    case App(_, expr, arg) if expr.info(Abstraction) contains abstraction =>
      (arg, None) ::
      recursiveArguments(expr, abstraction) ++
      recursiveArguments(arg, abstraction)
    case App(properties, expr, arg) =>
      recursiveArguments(expr, abstraction) ++
      recursiveArguments(arg, abstraction)
    case TypeAbs(ident, expr) =>
      recursiveArguments(expr, abstraction)
    case TypeApp(expr, tpe) =>
      recursiveArguments(expr, abstraction)
    case Data(ctor, args) =>
      args flatMap { recursiveArguments(_, abstraction) }
    case Var(ident) =>
      List.empty
    case Cases(scrutinee, cases) =>
      recursiveArguments(scrutinee, abstraction) ++
      (cases flatMap { (_, expr) => recursiveArguments(expr, abstraction) })
  end recursiveArguments
end DecreasingArguments
