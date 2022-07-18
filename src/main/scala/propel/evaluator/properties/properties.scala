package propel
package evaluator
package properties

import ast.*

object constraints:
  def derive(constraints: Set[(Term, Pattern)]): Set[(Term, Pattern)] =
    def start(
        constraints: Set[(Term, Pattern)],
        constraintsOld: Set[(Term, Pattern)],
        constraintsNew: Set[(Term, Pattern)]): Set[(Term, Pattern)] =
      if constraintsNew.nonEmpty then
        val derivedCompound =
          deriveCompound(constraintsOld, constraintsNew) ++
          deriveCompound(constraintsNew, constraintsNew)
        val derived = deriveSimple(constraintsNew ++ derivedCompound) -- constraints
        derived ++ start(constraints ++ derived, constraintsNew, derived)
      else
        Set.empty

    val derivedSimple = deriveSimple(constraints) -- constraints
    val aggregatedSimple = constraints ++ derivedSimple

    val derivedCompound = deriveCompound(aggregatedSimple, aggregatedSimple) -- aggregatedSimple
    val aggregatedCompound = aggregatedSimple ++ derivedCompound

    val derived = derivedSimple ++ derivedCompound
    derived ++ start(aggregatedCompound, aggregatedCompound, derived)

  def deriveSimple(constraints: Set[(Term, Pattern)]): Set[(Term, Pattern)] =
    Set.empty

  def deriveCompound(constraints0: Set[(Term, Pattern)], constraints1: Set[(Term, Pattern)]): Set[(Term, Pattern)] =
    (constraints0 collect {
      case App(properties2, App(properties1, expr, arg1), arg2) -> Match(Constructor.True, List())
          if properties1.contains(Transitive) =>
        constraints1 collect {
          case App(properties, App(`properties1`, expr, `arg2`), arg3) -> Match(Constructor.True, List()) =>
            App(properties, App(properties1, expr, arg1), arg3) -> Match(Constructor.True, List())
          case App(properties, App(`properties1`, expr, arg0), `arg1`) -> Match(Constructor.True, List()) =>
            App(properties, App(properties1, expr, arg0), arg2) -> Match(Constructor.True, List())
        }
    }).flatten
end constraints


object antisymmetry:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, arg0, Abs(_, arg1, expr)) =>
      val reversed = subst(expr, Map(arg0 -> Var(arg1), arg1 -> Var(arg0)))
      Abs(Set.empty, arg0, Abs(Set.empty, arg1, Util.implies(expr, Util.not(reversed))))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean = fun match
    case Abs(_, arg0, Abs(_, arg1, _)) =>
      result.reductions forall {
        case Symbolic.Reduction(Data(Constructor.True, _), _) =>
          true
        case Symbolic.Reduction(Data(Constructor.False, _), constraints) =>
          constraints.pos.get(Var(arg0)) == constraints.pos.get(Var(arg1)) ||
            (constraints refutable (constraints.pos collect {
              case App(properties1, App(properties0, expr, arg0), arg1) -> Match(Constructor.True, List())
                  if properties0.contains(Antisymmetric) =>
                App(properties1, App(properties0, expr, arg1), arg0) -> Match(Constructor.False, List())
            }))
        case _ =>
          false
      }
    case _ =>
      false


object transitivity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, arg0, Abs(_, arg1, expr)) =>
      val ab = subst(expr, Map(arg0 -> Var(Symbol("a")), arg1 -> Var(Symbol("b"))))
      val bc = subst(expr, Map(arg0 -> Var(Symbol("b")), arg1 -> Var(Symbol("c"))))
      val ac = subst(expr, Map(arg0 -> Var(Symbol("a")), arg1 -> Var(Symbol("c"))))
      Abs(Set.empty, Symbol("a"), Abs(Set.empty, Symbol("b"), Abs(Set.empty, Symbol("c"), Util.implies(Util.and(ab, bc), ac))))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(Data(Constructor.True, _), _) =>
        true
      case _ =>
        false
    }


object commutativity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, arg0, Abs(_, arg1, expr)) =>
      val reversed = subst(expr, Map(arg0 -> Var(arg1), arg1 -> Var(arg0)))
      Abs(Set.empty, arg0, Abs(Set.empty, arg1, Data(Constructor(Symbol("≟")), List(expr, reversed))))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(Data(Constructor(Symbol("≟")), List(arg0, arg1)), _) =>
        normalize(arg0) == normalize(arg1)
      case _ =>
        false
    }

  def normalize(expr: Term): Term = expr match
    case Abs(properties, arg, expr) =>
      Abs(properties, arg, normalize(expr))
    case App(properties1, App(properties0, expr, arg0), arg1) if properties0.contains(Commutative) =>
      val normalizedArg0 = normalize(arg0)
      val normalizedArg1 = normalize(arg1)
      if normalizedArg0 < normalizedArg1 then
        App(properties1, App(properties0, normalize(expr), normalizedArg0), normalizedArg1)
      else
        App(properties1, App(properties0, normalize(expr), normalizedArg1), normalizedArg0)
    case App(properties, expr, arg) =>
      App(properties, normalize(expr), normalize(arg))
    case Data(ctor, args) =>
      Data(ctor, args map normalize)
    case Var(ident) =>
      expr
    case Cases(scrutinee, cases) =>
      Cases(normalize(scrutinee), cases map { (pattern, expr) => pattern -> normalize(expr) })
