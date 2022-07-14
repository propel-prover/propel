package propel
package evaluator

import ast.*
import scala.annotation.targetName

object Symbolic:
  case class Constraints private (pos: PatternConstraints, neg: Set[PatternConstraints]):
    def refutable(constraints: Constraints): Boolean =
      constraints.pos unify this.pos forall { Constraints.refutable(_, constraints.neg ++ this.neg) }
    def refutable(pos: PatternConstraints): Boolean =
      pos unify this.pos forall { Constraints.refutable(_, this.neg) }
    def refutable(pos: IterableOnce[(Term, Pattern)]): Boolean =
      PatternConstraints.make(pos) flatMap { _ unify this.pos } forall { Constraints.refutable(_, this.neg) }

  object Constraints:
    def empty =
      Constraints(PatternConstraints.empty, Set.empty)
    def make(pos: PatternConstraints, neg: Set[PatternConstraints]): Option[Constraints] =
      Option.when(!refutable(pos, neg))(Constraints(pos, neg))

    private def refutable(pos: PatternConstraints, neg: Set[PatternConstraints]) =
      neg exists {
        _ forall { (expr, pattern) =>
          pos.get(expr) exists { !Unification.refutable(_, pattern) }
        }
      }

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
      case Match(ctor, args) => Data(ctor, args map { _.asTerm })
      case Bind(ident) => Var(ident)

  private def substConstraints(expr: Term, constraints: PatternConstraints): Term =
    replaceByConstraint(expr, constraints) match
      case term @ Abs(properties, arg, expr) =>
        Abs(term)(properties, arg, substConstraints(expr, constraints))
      case term @ App(properties, expr, arg) =>
        App(term)(properties, substConstraints(expr, constraints), substConstraints(arg, constraints))
      case term @ Data(ctor, args) =>
        Data(term)(ctor, args map { substConstraints(_, constraints) })
      case term @ Var(_) =>
        term
      case term @ Let(ident, bound, expr) =>
        Let(term)(ident, substConstraints(bound, constraints), substConstraints(expr, constraints))
      case term @ Cases(scrutinee, cases) =>
        Cases(term)(substConstraints(scrutinee, constraints), cases map { (pattern, expr) => pattern -> substConstraints(expr, constraints) })

  private def replaceByConstraint(expr: Term, constraints: PatternConstraints): Term =
    constraints.get(expr) match
      case Some(pattern) => replaceByConstraint(pattern.asTerm, constraints)
      case None => expr

  def eval(fun: Abs): Result =
    def contains(expr: Term, ident: Symbol): Boolean = expr match
      case Abs(_, _, expr) => contains(expr, ident)
      case App(_, expr, arg) => contains(expr, ident) || contains(arg, ident)
      case Data(_, args) => args exists { contains(_, ident) }
      case Let(_, bound, expr) => contains(bound, ident) || contains(expr, ident)
      case Cases(scrutinee, cases) => contains(scrutinee, ident) || (cases exists { (_, expr) => contains(expr, ident) })
      case Var(`ident`) => true
      case _ => false

    def complementConstraintsByProperties(constraints: PatternConstraints): Option[PatternConstraints] =
      PatternConstraints.make(properties.constraints.derive(constraints.toSet)) flatMap { _ unify constraints }

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
        case term @ Abs(properties, arg, expr) =>
          eval(expr, constraints) map { Abs(term)(properties, arg, _) }
        case term @ App(properties, expr, arg) =>
          evals(List(expr, arg), constraints) map { exprs => App(term)(properties, exprs.head, exprs.tail.head) }
        case term @ Data(ctor, args) =>
          evals(args, constraints) map { args => Data(term)(ctor, args) }
        case term @ Var(_) =>
          Result(List(Reduction(term, constraints)))
        case term @ Let(ident, bound, expr) =>
          if contains(bound, ident) then
            evals(List(bound, expr), constraints) map { exprs => Let(term)(ident, exprs.head, exprs.tail.head) }
          else
            eval(bound, constraints) flatMap { case Reduction(bound, constraints) =>
              eval(subst(expr, Map(ident -> bound)), constraints).reductions
            }
        case Cases(scrutinee, cases) =>
          eval(scrutinee, constraints) flatMap { case Reduction(scrutinee, constraints) =>
            def process(cases: List[(Pattern, Term)], constraints: Constraints): List[Reduction] = cases match
              case Nil => Nil
              case (pattern, expr) :: tail =>
                Unification.unify(pattern, scrutinee) match
                  case Unification.Full(substs) =>
                    eval(subst(expr, substs), constraints).reductions

                  case Unification.Irrefutable(substs, posConstraints) =>
                    val Constraints(pos, neg) = constraints
                    Unification.unify(posConstraints, pos) flatMap complementConstraintsByProperties flatMap { Constraints.make(_, neg) } match
                      case Some(constraints) =>
                        eval(subst(expr, substs), constraints).reductions ++ {
                          Constraints.make(pos, neg + posConstraints) map {
                            process(tail, _)
                          } getOrElse List.empty
                        }
                      case _ =>
                        process(tail, constraints)

                  case _ =>
                    process(tail, constraints)

            process(cases, constraints)
          }

    val result = eval(fun.expr, Constraints.empty)
    Result(result.reductions map { reduction => reduction map { substConstraints(_, reduction.constraints.pos) } })
  end eval
end Symbolic
