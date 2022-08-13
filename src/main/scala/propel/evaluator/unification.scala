package propel
package evaluator

import ast.*
import util.*
import scala.annotation.targetName


type PatternConstraints = Unification.Constraints

lazy val PatternConstraints: Unification.Constraints.type = Unification.Constraints


enum Unification:
  case Full(substs: TermSubstitutions)
  case Irrefutable(substs: TermSubstitutions, constraints: PatternConstraints)
  case Distinct

object Unification:
  opaque type Constraints <: Map[Term, Pattern] = Map[Term, Pattern]

  object Constraints:
    def empty: Constraints = Map.empty
    def make(expr: Term, pattern: Pattern): Constraints = Map(expr -> pattern)
    def make(constraints: IterableOnce[(Term, Pattern)]): Option[Constraints] =
      (constraints.iterator map { Map(_) }).reduceLeftIfDefinedOrElse(Map.empty) { unify(_, _) }

  extension (constraints: Constraints)
    @targetName("unifyConstraints")
    def unify(other: Constraints): Option[Constraints] = Unification.unify(constraints, other)
    @targetName("refutableConstraints")
    def refutable(other: Constraints): Boolean = Unification.refutable(constraints, other)
    @targetName("refutableConstraints")
    def refutable(other: IterableOnce[(Term, Pattern)]): Boolean =
      (((other.iterator map { Map(_) }) ++ Iterator(constraints)).reduceLeftIfDefinedOrElse(Map.empty) { _ unify _ }).isEmpty

  def unify(pattern: Pattern, expr: Term): Unification =
    def unify(pattern: Pattern, expr: Term): Option[(TermSubstitutions, Constraints)] =
      pattern -> expr match
        case Match(patternCtor, List()) -> Data(exprCtor, List()) =>
          Option.when(patternCtor == exprCtor)(Map.empty, Map.empty)
        case Match(patternCtor, patternArgs) -> Data(exprCtor, exprArgs) =>
          Option.when(patternCtor == exprCtor && patternArgs.size == exprArgs.size) {
            patternArgs zip exprArgs mapIfDefined unify flatMap { unified =>
              val (substss, constraintss) = unified.unzip
              constraintss.reduceLeftIfDefinedOrElse(Constraints.empty) { _ unify _ } map { (substss.mergeLeft, _) }
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
          unify(pattern, _) map { (pattern, constraints0, constraints1) =>
            constraints0 ++ constraints1 -> (expr, pattern)
          }
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

  def unify(pattern0: Pattern, pattern1: Pattern): Option[(Pattern, Constraints, Constraints)] =
    pattern0 -> pattern1 match
      case Match(ctor0, List()) -> Match(ctor1, List()) =>
        Option.when(ctor0 == ctor1)(pattern0, Map.empty, Map.empty)
      case Match(ctor0, args0) -> Match(ctor1, args1) =>
        Option.when(ctor0 == ctor1 && args0.size == args1.size) {
          args0 zip args1 mapIfDefined { unify(_, _) } flatMap { unified =>
            val (args, constraintss0, constraintss1) = unified.unzip3
            constraintss0.reduceLeftIfDefinedOrElse(Constraints.empty) { _ unify _ } flatMap { constraints0 =>
              constraintss1.reduceLeftIfDefinedOrElse(Constraints.empty) { _ unify _ } map {
                (Match(ctor0, args), constraints0, _)
              }
            }
          }
        }.flatten
      case Bind(ident0) -> Bind(ident1) if ident0 == ident1 =>
        Some(pattern0, Map.empty, Map.empty)
      case Bind(ident) -> _ =>
        Some(pattern1, Map(Var(pattern0)(ident) -> pattern1), Map.empty)
      case _ -> Bind(ident) =>
        Some(pattern0, Map.empty, Map(Var(pattern1)(ident) -> pattern0))

  def refutable(refutablePattern: Pattern, basePattern: Pattern): Boolean =
    unify(refutablePattern, basePattern) forall { (_, _, baseConstraints) => baseConstraints.nonEmpty }
end Unification
