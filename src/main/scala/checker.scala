package checker

import ast.*
import dsl.show
import ordering.given


def fail(message: String) = throw RuntimeException(message)


def unify(case0: Case, case1: Case): Option[Map[Ident.Term, Ident.Term]] = (case0, case1) match
  case (Case.Pattern(name0, args0), Case.Pattern(name1, args1)) =>
    if name0 == name1 && args0.size == args1.size then
      if args0.nonEmpty then
        args0 zip args1 map unify reduce {
          case (Some(subst0), Some(subst1)) => Some(subst0 ++ subst1)
          case _ => None
        }
      else
        Some(Map.empty)
    else
      None
  case (Case.Bind(name0), Case.Bind(name1)) =>
    Some(Map(name0 -> name1, name1 -> name0))
  case _ =>
    None


def computeSwaps(cases: List[(List[Case], Term)]): List[(Term, Map[Ident.Term, Ident.Term])] =
  type Swaps = Map[Ident.Term, Ident.Term]
  type Cases = List[(Case, Case, Term, Option[Swaps])]

  def computeSwapsCases(baseCase0: Case, baseCase1: Case, baseExpr: Term, cases: Cases): (Term, Swaps, Cases) = cases match
    case (head @ (case0, case1, expr, swaps)) :: tail =>
      val unification = swaps match
        case None => unify(baseCase0, case1) flatMap { swaps => unify(case0, baseCase1) map { _ ++ swaps } }
        case _ => None
      unification match
        case some @ Some(swaps) =>
          (expr, swaps, (case0, case1, baseExpr, some) :: tail)
        case None =>
          val (expr, swaps, cases) = computeSwapsCases(baseCase0, baseCase1, baseExpr, tail)
          (expr, swaps, head :: cases)
    case _ =>
      fail(s"Could not unify case: ${show(baseCase0)}")

  def computeSwaps(cases: Cases): List[(Term, Swaps)] = cases match
    case (baseCase0, baseCase1, baseExpr, None) :: _ =>
      val (expr, swaps, _ :: tail) = computeSwapsCases(baseCase0, baseCase1, baseExpr, cases)
      expr -> swaps :: computeSwaps(tail)
    case (_, _, expr, Some(swaps)) :: tail =>
      expr -> swaps :: computeSwaps(tail)
    case _ =>
      List.empty

  computeSwaps(cases map {
    case List(case0, case1) -> expr => (case0, case1, expr, None)
    case cases -> _ => fail(s"Two arguments expected but found pattern: ${show(cases)}")
  })


def swap(expr: Term, swaps: Map[Ident.Term, Ident.Term] = Map.empty): Term = expr match
  case Term.Abs(properties, cases) =>
    val swapped =
      if properties.contains(Property.Commutative) then
        cases zip computeSwaps(cases) map { case ((cases, _), (expr, exprswaps)) =>
          cases -> swap(expr, swaps ++ exprswaps)
        }
      else
        cases
    Term.Abs(properties, swapped)
  case Term.App(expr, args) =>
    Term.App(swap(expr), args map { swap(_, swaps) })
  case Term.Var(name) =>
    Term.Var(swaps.getOrElse(name, name))
  case Term.Ctor(name, args) =>
    Term.Ctor(name, args map { swap(_, swaps) })
  case Term.Let(properties, name, bound, expr) =>
    Term.Let(properties, name, swap(bound, swaps), swap(expr, swaps))


extension (context: Map[Ident.Term, Properties]) def contains(ident: Ident.Term, property: Property) =
  context.get(ident).exists(_.contains(property))


def normalize(expr: Term, context: Map[Ident.Term, Properties] = Map.empty): Term = expr match
  case Term.Abs(properties, cases) =>
    Term.Abs(properties, cases map { case cases -> expr => cases -> normalize(expr, context) })
  case Term.App(variable @ Term.Var(name), List(arg0, arg1)) if context.contains(name, Property.Commutative) =>
    if arg0 < arg1 then
      Term.App(variable, List(normalize(arg0, context), normalize(arg1, context)))
    else
      Term.App(variable, List(normalize(arg1, context), normalize(arg0, context)))
  case Term.App(expr, args) =>
    Term.App(normalize(expr, context), args map { normalize(_, context) })
  case Term.Var(_) =>
    expr
  case Term.Ctor(name, args) =>
    Term.Ctor(name, args map { normalize(_, context) })
  case Term.Let(properties, name, bound, expr) =>
    val extended = context + (name -> properties)
    Term.Let(properties, name, normalize(bound, extended), normalize(expr, extended))


def collectBindings(cases: List[Case]): Set[Ident.Term] = cases match
  case Case.Pattern(_, args) :: tail =>
    collectBindings(tail) ++ collectBindings(args)
  case Case.Bind(name) :: tail =>
    collectBindings(tail) + name
  case _ =>
    Set.empty


def checkValidity(expr: Term, context: Map[Ident.Term, Properties] = Map.empty): Unit = expr match
  case Term.Abs(properties, cases) =>
    cases foreach { (cases, expr) =>
      val bindings = collectBindings(cases)
      val existing = context.keySet & bindings
      if existing.nonEmpty then
        fail(s"Name clash: ${existing.map(_.name).mkString(", ")}")

      val extended = context ++ bindings.map(_ -> Set.empty)
      checkValidity(expr, context)
    }
  case Term.App(expr, args) =>
    checkValidity(expr, context)
    args foreach { checkValidity(_, context) }
  case Term.Var(_) =>
    ()
  case Term.Ctor(name, args) =>
    args foreach { checkValidity(_, context) }
  case Term.Let(properties, name, bound, expr) =>
    if properties.contains(Property.Commutative) then bound match
      case Term.Var(name) if !context.contains(name, Property.Commutative) =>
        fail("Cannot bind non-commutative value to commutative identifier")
      case Term.Abs(properties, _) if !properties.contains(Property.Commutative) =>
        fail("Cannot bind non-commutative value to commutative identifier")
      case _ =>

    if context.contains(name) then
      fail(s"Name clash: ${name.name}")

    val extended = context + (name -> properties)
    checkValidity(bound, extended)
    checkValidity(expr, extended)

def checkCommutativity(expr: Term): Unit =
  if normalize(expr) != normalize(swap(expr)) then fail("Cannot prove commutativity")

def check(expr: Term): Unit =
  checkValidity(expr)
  checkCommutativity(expr)
