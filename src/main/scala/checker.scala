package checker

import ast.*
import util.*
import impl.*
import ordering.given
import scala.annotation.targetName
import scala.collection.mutable


package impl:
  def fail(message: String) = throw RuntimeException(message)

  def subscript(i: Int) =
    def subscript(i: Int) = i.toString map { c => (c.toInt - '0' + '₀').toChar }
    if i < 0 then "₋" + subscript(-i) else subscript(i)


def alpharename(expr: Term): Term =
  val used = mutable.Set.empty[Symbol]

  def freshIdent(base: Symbol, index: Int): Symbol =
    val ident = Symbol(base.name + subscript(index))
    if used.contains(ident) then
      freshIdent(base, index + 1)
    else
      used += ident
      ident

  def renameCase(pattern: Pattern): (Pattern, Map[Symbol, Symbol]) = pattern match
    case Match(ctor, args) =>
      val (renamedArgs, substs) = args.map(renameCase).unzip
      (Match(ctor, renamedArgs), substs.foldLeft(Map.empty) { _ ++ _ })
    case Bind(ident) =>
      val fresh = freshIdent(ident, 1)
      (Bind(fresh), Map(ident -> fresh))

  def renameTerm(expr: Term, subst: Map[Symbol, Symbol]): Term = expr match
    case Abs(properties, args, expr) =>
      val (renamedArgs, additionalSubst) = (args map { arg =>
        val fresh = freshIdent(arg, 1)
        (fresh, arg -> fresh)
      }).unzip
      Abs(properties, renamedArgs, renameTerm(expr, subst ++ additionalSubst))
    case App(properties, ctor: Constructor, args) =>
      App(properties, ctor, args map { renameTerm(_, subst) })
    case App(properties, expr: Term, args) =>
      App(properties, renameTerm(expr, subst), args map { renameTerm(_, subst) })
    case Var(ident) =>
      subst.get(ident) map { Var(_) } getOrElse expr
    case Let(ident, bound, expr) =>
      val fresh = freshIdent(ident, 1)
      Let(fresh, renameTerm(bound, subst + (ident -> fresh)), renameTerm(expr, subst + (ident -> fresh)))
    case Cases(scrutinee, cases) =>
      val renamedScrutinee = renameTerm(scrutinee, subst)
      val renamedCases = cases map { (pattern, expr) =>
        val (renamedPattern, additionalSubst) = renameCase(pattern)
        renamedPattern -> renameTerm(expr, subst ++ additionalSubst)
      }
      Cases(renamedScrutinee, renamedCases)

  renameTerm(expr, Map.empty)


def subst(expr: Term, substs: Map[Symbol, Term]): Term =
  substs foreach { (ident, bound) =>
    def countIdent(expr: Term, ident: Symbol): Int = expr match
      case Abs(_, args, expr) => countIdent(expr, ident)
      case App(_, _: Constructor, args) => (args map { countIdent(_, ident) }).sum
      case App(_, expr: Term, args) => countIdent(expr, ident) + (args map { countIdent(_, ident) }).sum
      case Let(_, bound, expr) => countIdent(bound, ident) + countIdent(expr, ident)
      case Cases(scrutinee, cases) => countIdent(scrutinee, ident) + (cases map { (_, expr) => countIdent(expr, ident) }).sum
      case Var(`ident`) => 1
      case _ => 0

    def containsLambda(expr: Term): Boolean = expr match
      case Abs(_, _ :: _, _) => true
      case App(_, _: Constructor, args) => args exists containsLambda
      case App(_, expr: Term, args) => containsLambda(expr) || (args exists containsLambda)
      case Let(_, bound, expr) => containsLambda(bound) || containsLambda(expr)
      case Cases(scrutinee, cases) => containsLambda(scrutinee) || (cases exists { (_, expr) => containsLambda(expr) })
      case _ => false

    if containsLambda(bound) && countIdent(expr, ident) > 1 then
      fail("Implementation restriction: "+
        s"expression bound to ${ident.name} cannot be used multiple times because it contains non-constant lambda expressions")
  }

  def bound(pattern: Pattern): List[Symbol] = pattern match
    case Match(_, args) => args flatMap bound
    case Bind(ident) => List(ident)

  def subst(expr: Term, substs: Map[Symbol, Term]): Term = expr match
    case Abs(properties, args, expr) =>
      Abs(properties, args, subst(expr, substs -- args))
    case App(properties, ctor: Constructor, args) =>
      App(properties, ctor, args map { subst(_, substs) })
    case App(properties, expr: Term, args) =>
      App(properties, subst(expr, substs), args map { subst(_, substs) })
    case Var(ident) =>
      substs.getOrElse(ident, expr)
    case Let(ident, bound, expr) =>
      Let(ident, subst(bound, substs), subst(expr, substs - ident))
    case Cases(scrutinee, cases) =>
      Cases(
        subst(scrutinee, substs),
        cases map { (pattern, expr) =>
          pattern -> subst(expr, substs -- bound(pattern))
        })

  subst(expr, substs)


def subst(pattern: Pattern, substs: Map[Symbol, Pattern]): Pattern = pattern match
  case Match(ctor, args) =>
    Match(ctor, args map { subst(_, substs) })
  case Bind(ident) =>
    substs.getOrElse(ident, pattern)


enum Unification:
  case Full(substs: Map[Symbol, Term])
  case Irrefutable(substs: Map[Symbol, Term], constraints: Map[Term, Pattern])
  case Distinct

object Unification:
  type Constraints = Map[Term, Pattern]

  type Substitutions = Map[Symbol, Term]

  def unify(pattern: Pattern, expr: Term): Unification =
    def unify(pattern: Pattern, expr: Term): Option[(Substitutions, Constraints)] =
      pattern -> expr match
        case Match(patternCtor, List()) -> App(_, exprCtor: Constructor, List()) =>
          Option.when(patternCtor == exprCtor)(Map.empty, Map.empty)
        case Match(patternCtor, patternArgs) -> App(_, exprCtor: Constructor, exprArgs) =>
          Option.when(patternCtor == exprCtor && patternArgs.size == exprArgs.size) {
            patternArgs zip exprArgs mapIfDefined unify flatMap { unified =>
              val (substss, constraintss) = unified.unzip
              constraintss reduceLeftIfDefined Unification.unify map { (substss.mergeLeft, _) }
            }
          }.flatten
        case Bind(ident) -> expr =>
          Some(Map(ident -> expr), Map.empty)
        case _=>
          Some(Map.empty, Map(expr -> pattern))

    unify(pattern, expr) match
      case Some(substs, constraints) if constraints.isEmpty => Full(substs)
      case Some(substs, constraints) => Irrefutable(substs, constraints)
      case _ => Distinct

  def refutable(pattern: Pattern, expr: Term): Boolean =
    unify(pattern, expr) == Distinct

  def unify(constraints0: Constraints, constraints1: Constraints): Option[Constraints] =
    def merge(constraints0: Constraints, constraints1: Constraints): Option[Constraints] =
      val unified = constraints0 flatMap { (expr, pattern) =>
        constraints1.get(expr) map {
          unify(pattern, _) map { case (pattern, constraints) => constraints -> (expr, pattern) }
        }
      }

      unified.sequenceIfDefined flatMap { unified =>
        val (constraintss, constraints2) = unified.unzip
        val constraints = constraintss.mergeLeft
        if constraints.nonEmpty then
          merge(constraints0 ++ constraints1 ++ constraints2, constraints)
        else
          Some(constraints0 ++ constraints1 ++ constraints2)
      }

    def propagate(constraints: Constraints): Constraints =
      val substs = constraints collect { case Var(ident) -> pattern => ident -> pattern }
      val propagated = (constraints.view mapValues { subst(_, substs) }).toMap
      if constraints != propagated then propagate(propagated) else propagated

    if constraints0.isEmpty || constraints1.isEmpty then
      Some(constraints0 ++ constraints1)
    else
      merge(constraints0, constraints1) map propagate

  def refutable(constraints0: Constraints, constraints1: Constraints): Boolean =
    unify(constraints0, constraints1).isEmpty

  def unify(pattern0: Pattern, pattern1: Pattern): Option[(Pattern, Constraints)] =
    pattern0 -> pattern1 match
      case Match(ctor0, List()) -> Match(ctor1, List()) =>
        Option.when(ctor0 == ctor1)(pattern0, Map.empty)
      case Match(ctor0, args0) -> Match(ctor1, args1) =>
        Option.when(ctor0 == ctor1 && args0.size == args1.size) {
          args0 zip args1 mapIfDefined { unify(_, _) } flatMap { unified =>
            val (args, constraintss) = unified.unzip
            constraintss reduceLeftIfDefined { unify(_, _) } map { (Match(ctor0, args), _) }
          }
        }.flatten
      case Bind(ident0) -> Bind(ident1) if ident0 == ident1 =>
        Some(pattern0, Map.empty)
      case _ -> Bind(ident) =>
        Some(pattern0, Map(Var(ident) -> pattern0))
      case Bind(ident) -> _ =>
        Some(pattern1, Map(Var(ident) -> pattern1))

  def refutable(pattern0: Pattern, pattern1: Pattern): Boolean =
    unify(pattern0, pattern1).isEmpty
end Unification



object Symbolic:
  case class Constraints(pos: Map[Term, Pattern], neg: Set[Map[Term, Pattern]])

  case class Result(reductions: List[Reduction]) extends AnyVal

  case class Reduction(expr: Term, constraints: Constraints)

  private case class Results(reductions: List[Reductions]) extends AnyVal

  private case class Reductions(exprs: List[Term], constraints: Constraints)

  extension (result: Result)
    @targetName("flatMapResult")
    private inline def flatMap(f: Reduction => List[Reduction]): Result = result.copy(result.reductions flatMap f)
    @targetName("mapResult")
    private inline def map(f: Term => Term): Result = result.copy(result.reductions map { _ map f })

  extension (reduction: Reduction)
    private inline def map(f: Term => Term): Reduction = reduction.copy(expr = f(reduction.expr))

  extension (results: Results)
    private inline def map(f: List[Term] => Term): Result = Result(results.reductions map { _ map f })
    private inline def flatMap(f: Reductions => List[Reductions]): Results = results.copy(results.reductions flatMap f)

  extension (reductions: Reductions)
    private inline def map(f: List[Term] => Term): Reduction = Reduction(f(reductions.exprs), reductions.constraints)
    private inline def flatMap(f: Term => List[Term]): Reductions = reductions.copy(exprs = reductions.exprs flatMap f)

  extension (pattern: Pattern)
    private def asTerm: Term = pattern match
      case Match(ctor, args) => App(Set.empty, ctor, args map { _.asTerm })
      case Bind(ident) => Var(ident)

  private def refutable(pos: Map[Term, Pattern], neg: Set[Map[Term, Pattern]]) =
    neg exists {
      _ forall { (expr, pattern) =>
        pos.get(expr) exists { !Unification.refutable(_, pattern) }
      }
    }

  private def substConstraints(expr: Term, constraints: Map[Term, Pattern]): Term =
    replaceByConstraint(expr, constraints) match
      case Abs(properties, args, expr) =>
        Abs(properties, args, substConstraints(expr, constraints))
      case App(properties, ctor: Constructor, args) =>
        App(properties, ctor, args map { substConstraints(_, constraints) })
      case App(properties, expr: Term, args) =>
        App(properties, substConstraints(expr, constraints), args map { substConstraints(_, constraints) })
      case Var(_) =>
        expr
      case Let(ident, bound, expr) =>
        Let(ident, substConstraints(bound, constraints), substConstraints(expr, constraints))
      case Cases(scrutinee, cases) =>
        Cases(substConstraints(scrutinee, constraints), cases map { (pattern, expr) => pattern -> substConstraints(expr, constraints) })

  private def replaceByConstraint(expr: Term, constraints: Map[Term, Pattern]): Term =
    constraints.get(expr) match
      case Some(pattern) => replaceByConstraint(pattern.asTerm, constraints)
      case None => expr

  def eval(fun: Abs): Result =
    def contains(expr: Term, ident: Symbol): Boolean = expr match
      case Abs(_, args, expr) => contains(expr, ident)
      case App(_, _: Constructor, args) => args exists { contains(_, ident) }
      case App(_, expr: Term, args) => contains(expr, ident) || (args exists { contains(_, ident) })
      case Let(_, bound, expr) => contains(bound, ident) || contains(expr, ident)
      case Cases(scrutinee, cases) => contains(scrutinee, ident) || (cases exists { (_, expr) => contains(expr, ident) })
      case Var(`ident`) => true
      case _ => false

    def complementConstraintsByProperties(constraints: Map[Term, Pattern]): Option[Map[Term, Pattern]] =
      (constraintsByProperties.derive(constraints.toSet).toList map { Map(_) }) :+ constraints reduceLeftIfDefined Unification.unify

    def evals(exprs: List[Term], constraints: Constraints): Results =
      exprs.foldLeft(Results(List(Reductions(List.empty, constraints)))) { (results, expr) =>
        results flatMap { case Reductions(exprs, constraints) =>
          eval(expr, constraints).reductions map { case Reduction(expr, constraints) =>
            Reductions(exprs :+ expr, constraints)
          }
        }
      }

    def eval(expr: Term, constraints: Constraints): Result =
      replaceByConstraint(expr, constraints.pos) match
        case Abs(properties, args, expr) =>
          eval(expr, constraints) map { Abs(properties, args, _) }
        case App(properties, ctor: Constructor, args) =>
          evals(args, constraints) map { args => App(properties, ctor, args) }
        case App(properties, expr: Term, args) =>
          evals(expr :: args, constraints) map { args => App(properties, args.head, args.tail) }
        case Var(_) =>
          Result(List(Reduction(expr, constraints)))
        case Let(ident, bound, expr) =>
          if contains(bound, ident) then
            evals(List(bound, expr), constraints) map { exprs => Let(ident, exprs.head, exprs.tail.head) }
          else
            eval(bound, constraints) flatMap { case Reduction(bound, constraints) =>
              eval(subst(expr, Map(ident -> bound)), constraints).reductions
            }
        case Cases(scrutinee, cases) =>
          eval(scrutinee, constraints) flatMap { case Reduction(scrutinee, constraints @ Constraints(pos, neg)) =>
            def process(cases: List[(Pattern, Term)], constraints: Constraints): List[Reduction] = cases match
              case Nil => Nil
              case (pattern, expr) :: tail =>
                Unification.unify(pattern, scrutinee) match
                  case Unification.Full(substs) =>
                    eval(subst(expr, substs), constraints).reductions

                  case Unification.Irrefutable(substs, posConstraints) =>
                    val Constraints(pos, neg) = constraints
                    Unification.unify(posConstraints, pos) flatMap complementConstraintsByProperties match
                      case Some(posUnified) if !refutable(posUnified, neg) =>
                        eval(subst(expr, substs), Constraints(posUnified, neg)).reductions ++ {
                          if (!refutable(pos, neg + posConstraints))
                            process(tail, Constraints(pos, neg + posConstraints))
                          else
                            List.empty
                        }
                      case _ =>
                        process(tail, constraints)

                  case _ =>
                    process(tail, constraints)

            process(cases, constraints)
          }

    val result = eval(fun.expr, Constraints(Map.empty, Set.empty))
    Result(result.reductions map { reduction => reduction map { substConstraints(_, reduction.constraints.pos) } })
  end eval
end Symbolic


object constraintsByProperties:
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
      case App(properties, expr, List(arg1, arg2)) -> Match(Constructor.True, List())
          if properties.contains(Transitive) =>
        constraints1 collect {
          case App(`properties`, `expr`, List(`arg2`, arg3)) -> Match(Constructor.True, List()) =>
            App(properties, expr, List(arg1, arg3)) -> Match(Constructor.True, List())
          case App(`properties`, `expr`, List(arg0, `arg1`)) -> Match(Constructor.True, List()) =>
            App(properties, expr, List(arg0, arg2)) -> Match(Constructor.True, List())
        }
    }).flatten
end constraintsByProperties


package connectors:
  def implies(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> b,
    Match(Constructor.False, List.empty) -> App(Set.empty, Constructor.True, List.empty)))

  def or(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> App(Set.empty, Constructor.True, List.empty),
    Match(Constructor.False, List.empty) -> b))

  def and(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> b,
    Match(Constructor.False, List.empty) -> App(Set.empty, Constructor.False, List.empty)))

  def not(a: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> App(Set.empty, Constructor.False, List.empty),
    Match(Constructor.False, List.empty) -> App(Set.empty, Constructor.True, List.empty)))

import connectors.*


object antisymmetry:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, List(arg0, arg1), expr) =>
      val reversed = subst(expr, Map(arg0 -> Var(arg1), arg1 -> Var(arg0)))
      Abs(Set.empty, List(arg0, arg1), implies(expr, not(reversed)))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean = fun.args match
    case List(arg0, arg1) =>
      result.reductions forall {
        case Symbolic.Reduction(App(_, Constructor.True, _), _) =>
          true
        case Symbolic.Reduction(App(_, Constructor.False, _), constraints) =>
          constraints.pos.get(Var(arg0)) == constraints.pos.get(Var(arg1)) ||
            Unification.refutable(constraints.pos, constraints.pos collect {
              case App(properties, expr, List(arg0, arg1)) -> Match(Constructor.True, List())
                  if properties.contains(Antisymmetric) =>
                App(properties, expr, List(arg1, arg0)) -> Match(Constructor.False, List())
            })
        case _ =>
          false
      }
    case _ =>
      false


object transitivity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, List(arg0, arg1), expr) =>
      val ab = subst(expr, Map(arg0 -> Var(Symbol("a")), arg1 -> Var(Symbol("b"))))
      val bc = subst(expr, Map(arg0 -> Var(Symbol("b")), arg1 -> Var(Symbol("c"))))
      val ac = subst(expr, Map(arg0 -> Var(Symbol("a")), arg1 -> Var(Symbol("c"))))
      Abs(Set.empty, List(Symbol("a"), Symbol("b"), Symbol("c")), implies(and(ab, bc), ac))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(App(_, Constructor.True, _), _) =>
        true
      case _ =>
        false
    }


object commutativity:
  def prepare(fun: Abs): Abs = fun match
    case Abs(_, List(arg0, arg1), expr) =>
      val reversed = subst(expr, Map(arg0 -> Var(arg1), arg1 -> Var(arg0)))
      Abs(Set.empty, List(arg0, arg1), App(Set.empty, Constructor(Symbol("≟")), List(expr, reversed)))
    case _ =>
      fun

  def check(name: String, fun: Abs, result: Symbolic.Result): Boolean =
    result.reductions forall {
      case Symbolic.Reduction(App(_, Constructor(Symbol("≟")), List(arg0, arg1)), _) =>
        normalize(arg0) == normalize(arg1)
      case _ =>
        false
    }

  def normalize(expr: Term): Term = expr match
    case Abs(properties, args, expr) =>
      Abs(properties, args, normalize(expr))
    case App(properties, expr: Term, List(arg0, arg1)) if properties.contains(Commutative) =>
      val normalizedArg0 = normalize(arg0)
      val normalizedArg1 = normalize(arg1)
      if normalizedArg0 < normalizedArg1 then
        App(properties, normalize(expr), List(normalizedArg0, normalizedArg1))
      else
        App(properties, normalize(expr), List(normalizedArg1, normalizedArg0))
    case App(properties, expr: Term, args) =>
      App(properties, normalize(expr), args map normalize)
    case App(properties, ctor: Constructor, args) =>
      App(properties, ctor, args map normalize)
    case Var(ident) =>
      expr
    case Let(ident, bound, expr) =>
      Let(ident, normalize(bound), normalize(expr))
    case Cases(scrutinee, cases) =>
      Cases(normalize(scrutinee), cases map { (pattern, expr) => pattern -> normalize(expr) })
