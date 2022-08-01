package propel
package evaluator
package properties

import ast.*

object equalities:
  def derive(equalities: Equalities): Option[Equalities] =
    equalities.withEqualities(antisymmetry.derive(equalities) ++ transitivity.derive(equalities)) flatMap { updated =>
      if updated != equalities then derive(updated) else Some(updated)
    }


object antisymmetry:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, ident0, tpe0, Abs(_, ident1, tpe1, expr)) =>
      val reversed = subst(expr, Map(ident0 -> Var(ident1), ident1 -> Var(ident0)))
      Abs(Set.empty, ident0, tpe0, Abs(Set.empty, ident1, tpe0, Util.implies(expr, Util.not(reversed))))
    case _ =>
      fun

  def derive(equalities: Equalities): List[(Term, Term)] =
    equalities.pos.toList collect {
      case App(properties1, App(properties0, expr, arg0), arg1) -> Data(Constructor.True, List())
          if properties0.contains(Antisymmetric) && equalities.equal(arg0, arg1) == Equality.Unequal =>
        App(properties1, App(properties0, expr, arg1), arg0) -> Data(Constructor.False, List())
    }

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(Data(Constructor.True, _), _, _) =>
        true
      case _ =>
        false
    }


object transitivity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, ident0, tpe0, Abs(_, ident1, tpe1, expr)) =>
      val ab = subst(expr, Map(ident0 -> Var(Symbol("a")), ident1 -> Var(Symbol("b"))))
      val bc = subst(expr, Map(ident0 -> Var(Symbol("b")), ident1 -> Var(Symbol("c"))))
      val ac = subst(expr, Map(ident0 -> Var(Symbol("a")), ident1 -> Var(Symbol("c"))))
      Abs(Set.empty, Symbol("a"), tpe0, Abs(Set.empty, Symbol("b"), tpe0, Abs(Set.empty, Symbol("c"), tpe0, Util.implies(Util.and(ab, bc), ac))))
    case _ =>
      fun

  def derive(equalities: Equalities): List[(Term, Term)] =
    (equalities.pos.toList collect {
      case App(properties2, App(properties1, expr0, arg1), arg2) -> Data(Constructor.True, List())
          if properties1.contains(Transitive) =>
        equalities.pos.toList collect {
          case App(properties, App(`properties1`, expr1, `arg2`), arg3) -> Data(Constructor.True, List())
              if equivalent(expr0, expr1) =>
            App(properties, App(properties1, expr1, arg1), arg3) -> Data(Constructor.True, List())
          case App(properties, App(`properties1`, expr1, arg0), `arg1`) -> Data(Constructor.True, List())
              if equivalent(expr0, expr1) =>
            App(properties, App(properties1, expr1, arg0), arg2) -> Data(Constructor.True, List())
        }
    }).flatten

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(Data(Constructor.True, _), _, _) =>
        true
      case _ =>
        false
    }


object commutativity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, ident0, tpe0, Abs(_, ident1, tpe1, expr)) =>
      val reversed = subst(expr, Map(ident0 -> Var(ident1), ident1 -> Var(ident0)))
      Abs(Set.empty, ident0, tpe0, Abs(Set.empty, ident1, tpe0, Data(Constructor(Symbol("≟")), List(expr, reversed))))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(Data(Constructor(Symbol("≟")), List(arg0, arg1)), _, _) =>
        normalize(arg0) == normalize(arg1)
      case _ =>
        false
    }

  def normalize(term: Term): Term = term match
    case Abs(properties, ident, tpe, expr) =>
      Abs(term)(properties, ident, tpe, normalize(expr))
    case App(properties1, App(properties0, expr, arg0), arg1) if properties0.contains(Commutative) =>
      val normalizedArg0 = normalize(arg0)
      val normalizedArg1 = normalize(arg1)
      if normalizedArg0 < normalizedArg1 then
        App(term)(properties1, App(properties0, normalize(expr), normalizedArg0), normalizedArg1)
      else
        App(term)(properties1, App(properties0, normalize(expr), normalizedArg1), normalizedArg0)
    case App(properties, expr, arg) =>
      App(term)(properties, normalize(expr), normalize(arg))
    case TypeAbs(ident, expr) =>
      TypeAbs(term)(ident, normalize(expr))
    case TypeApp(expr, tpe) =>
      TypeApp(term)(normalize(expr), tpe)
    case Data(ctor, args) =>
      Data(term)(ctor, args map normalize)
    case Var(_) =>
      term
    case Cases(scrutinee, cases) =>
      Cases(term)(normalize(scrutinee), cases map { (pattern, expr) => pattern -> normalize(expr) })
