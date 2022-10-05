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
          Option.when(patternCtor == exprCtor && patternArgs.sizeCompare(exprArgs) == 0) {
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

    def contains(pattern: Pattern, identx: Symbol): Boolean = pattern match
      case Match(ctor, args) => args exists { contains(_, identx) }
      case Bind(ident) => ident == identx

    def propagate(constraints: Constraints): Constraints =
      val substs = constraints collect { case Var(ident) -> pattern if !contains(pattern, ident) => ident -> pattern }
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
        Option.when(ctor0 == ctor1 && args0.sizeCompare(args1) == 0) {
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

  def unify(expr0: Term, expr1: Term): Option[(TermSubstitutions, TermSubstitutions)] =
    inline def merge(inline substs0: TermSubstitutions, inline substs1: TermSubstitutions) =
      Option.when(!(substs0.keys exists { substs1 contains _ }))(substs0 ++ substs1)

    def patternSubsts(pattern0: Pattern, pattern1: Pattern, used: Set[String]): Option[(TermSubstitutions, TermSubstitutions, Set[String])] =
      pattern0 -> pattern1 match
        case Match(ctor0, args0) -> Match(ctor1, args1) if ctor0 == ctor1 =>
          (args0 zip args1).foldLeft[Option[(TermSubstitutions, TermSubstitutions, Set[String])]](Some(Map.empty, Map.empty, used)) {
            case (Some(substs0, substs1, used), (arg0, arg1)) =>
              patternSubsts(arg0, arg1, used) map { (argSubsts0, argSubsts1, used) => (substs0 ++ argSubsts0, substs1 ++ argSubsts1, used) }
            case _ =>
              None
          }
        case Bind(ident0) -> Bind(ident1) =>
          if ident0 != ident1 then
            val ident = Naming.freshIdent(ident0, used)
            Some(Map(ident0 -> Var(ident)), Map(ident1 -> Var(ident)), used + ident.name)
          else
            Some(Map.empty, Map.empty, used)
        case _ =>
          None

    def unify(expr0: Term, expr1: Term, used: Set[String], typeSubsts: TypeSubstitutions): Option[(TermSubstitutions, TermSubstitutions, Set[String])] =
      expr0 -> expr1 match
        case Abs(_, ident0, tpe0, expr0) -> Abs(_, ident1, tpe1, expr1) if equivalent(tpe0, subst(tpe1, typeSubsts)) =>
          if ident0 != ident1 then
            val ident = Naming.freshIdent(ident0, used)
            unify(subst(expr0, Map(ident0 -> Var(ident))), subst(expr1, Map(ident1 -> Var(ident))), used + ident.name, typeSubsts)
          else
            unify(expr0, expr1, used, typeSubsts)
        case App(_, expr0, arg0) -> App(_, expr1, arg1) =>
          unify(expr0, expr1, used, typeSubsts) flatMap { (exprSubsts0, exprSubsts1, used) =>
            unify(arg0, arg1, used, typeSubsts) flatMap { (argSubsts0, argSubsts1, used) =>
              merge(exprSubsts0, argSubsts0) flatMap { substs0 =>
                merge(exprSubsts1, argSubsts1) map { (substs0, _, used) }
              }
            }
          }
        case TypeAbs(ident0, expr0) -> TypeAbs(ident1, expr1) =>
          if ident0 != ident1 then
            unify(expr0, expr1, used, typeSubsts + (ident1 -> TypeVar(ident0)))
          else
            unify(expr0, expr1, used, typeSubsts)
        case TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) if equivalent(tpe0, subst(tpe1, typeSubsts)) =>
          unify(expr0, expr1, used, typeSubsts)
        case Data(ctor0, args0) -> Data(ctor1, args1) if ctor0 == ctor1 =>
          (args0 zip args1).foldLeft[Option[(TermSubstitutions, TermSubstitutions, Set[String])]](Some(Map.empty, Map.empty, used)) {
            case (Some(substs0, substs1, used), (arg0, arg1)) =>
              unify(arg0, arg1, used, typeSubsts) flatMap { (argSubsts0, argSubsts1, used) =>
                merge(substs0, argSubsts0) flatMap { substs0 =>
                  merge(substs1, argSubsts1) map { (substs0, _, used) }
                }
              }
            case _ =>
              None
          }
        case Cases(scrutinee0, cases0) -> Cases(scrutinee1, cases1) =>
          (cases0 zip cases1).foldLeft(unify(scrutinee0, scrutinee1, used, typeSubsts)) {
            case (Some(substs0, substs1, used), (pattern0 -> expr0, pattern1 -> expr1)) =>
              patternSubsts(pattern0, pattern1, used) flatMap { (substs0, substs1, used) =>
                unify(subst(expr0, substs0), subst(expr1, substs1), used, typeSubsts) flatMap { (exprSubsts0, exprSubsts1, used) =>
                  merge(substs0, exprSubsts0) flatMap { substs0 =>
                    merge(substs1, exprSubsts1) map { (substs0, _, used) }
                  }
                }
              }
            case _ =>
              None
          }
        case Var(ident0) -> _ =>
          Some(Map(ident0 -> expr1), Map.empty, used)
        case _ -> Var(ident1) =>
          Some(Map.empty, Map(ident1 -> expr0), used)
        case _ =>
          None

    val expr0Info = expr0.syntacticInfo
    val expr1Info = expr1.syntacticInfo
    val used = expr0Info.boundVars ++ expr0Info.freeVars.keySet ++ expr1Info.boundVars ++ expr1Info.freeVars.keySet map { _.name }

    def containsOnlyUsed(expr: Term): Boolean = expr match
      case Abs(_, _, _, expr) => containsOnlyUsed(expr)
      case App(_, expr, arg) => containsOnlyUsed(expr) && containsOnlyUsed(arg)
      case TypeAbs(_, expr) => containsOnlyUsed(expr)
      case TypeApp(expr, _) => containsOnlyUsed(expr)
      case Data(_, args) => args forall containsOnlyUsed
      case Var(ident) => used contains ident.name
      case Cases(scrutinee, cases) => containsOnlyUsed(scrutinee) && (cases forall { (_, expr) => containsOnlyUsed(expr) })

    def validSubsts(substs: TermSubstitutions) =
      val filtered = substs filter {
        case (ident, Var(exprIdent)) => ident != exprIdent || (used contains ident.name)
        case _ => true
      }
      Option.when(filtered forall { (ident, expr) => (used contains ident.name) && containsOnlyUsed(expr) })(filtered)

    unify(expr0, expr1, used, Map.empty) flatMap { (substs0, substs1, _) =>
      validSubsts(substs0) flatMap { substs0 =>
        validSubsts(substs1) map { (substs0, _) }
      }
    }

  def refutable(refutableExpr: Term, baseExpr: Term): Boolean =
    unify(refutableExpr, baseExpr) forall { (_, baseConstraints) => baseConstraints.nonEmpty }
end Unification
