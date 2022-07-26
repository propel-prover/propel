package propel
package evaluator

import ast.*
import typer.*
import scala.annotation.targetName

object Symbolic:
  case class Constraints private (pos: PatternConstraints, neg: Set[PatternConstraints]):
    def refutable(constraints: Constraints): Boolean =
      constraints.pos unify this.pos forall { pos =>
        val neg = constraints.neg ++ this.neg
        Constraints.refutablePosNeg(pos, neg) || Constraints.refutableNegTyped(neg)
      }
    def refutable(pos: PatternConstraints): Boolean =
      pos unify this.pos forall { Constraints.refutablePosNeg(_, this.neg) }
    def refutable(pos: IterableOnce[(Term, Pattern)]): Boolean =
      PatternConstraints.make(pos) flatMap { _ unify this.pos } forall { Constraints.refutablePosNeg(_, this.neg) }

  object Constraints:
    def empty =
      Constraints(PatternConstraints.empty, Set.empty)
    def make(pos: PatternConstraints, neg: Set[PatternConstraints]): Option[Constraints] =
      Option.when(!refutablePosNeg(pos, neg) && !refutableNegTyped(neg))(Constraints(pos, neg))

    private def refutablePosNeg(pos: PatternConstraints, neg: Set[PatternConstraints]) =
      neg exists {
        _ forall { (expr, pattern) =>
          pos.get(expr) exists { !Unification.refutable(_, pattern) }
        }
      }

    private def refutableNegTyped(neg: Set[PatternConstraints]) =
      val negTermConstraints = neg.foldLeft(List(Map.empty[Term, List[Pattern]])) { (negTermConstraints, neg) =>
        (neg flatMap { (expr, pattern) =>
          negTermConstraints map { _.updatedWith(expr) { _ map { pattern :: _ } orElse Some(List(pattern)) } }
        }).toList
      }

      negTermConstraints forall {
        _ exists { (expr, patterns) =>
          expr.typed match
            case (_, Some(tpe)) =>
              patterns.foldLeft(tpe) { (tpe, pattern) => diff(tpe, pattern) getOrElse tpe } match
                case Sum(List()) => true
                case _ => false
            case _ =>
              false
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
      case Bind(ident) => Var(pattern)(ident)

  private def substConstraints(expr: Term, constraints: PatternConstraints): Term =
    replaceByConstraint(expr, constraints) match
      case term @ Abs(properties, ident, tpe, expr) =>
        Abs(term)(properties, ident, tpe, substConstraints(expr, constraints))
      case term @ App(properties, expr, arg) =>
        App(term)(properties, substConstraints(expr, constraints), substConstraints(arg, constraints))
      case term @ TypeAbs(ident, expr) =>
        TypeAbs(term)(ident, substConstraints(expr, constraints))
      case term @ TypeApp(expr, tpe) =>
        TypeApp(term)(substConstraints(expr, constraints), tpe)
      case term @ Data(ctor, args) =>
        Data(term)(ctor, args map { substConstraints(_, constraints) })
      case term @ Var(_) =>
        term
      case term @ Cases(scrutinee, cases) =>
        Cases(term)(substConstraints(scrutinee, constraints), cases map { (pattern, expr) => pattern -> substConstraints(expr, constraints) })

  private def replaceByConstraint(expr: Term, constraints: PatternConstraints): Term =
    constraints.get(expr) match
      case Some(pattern) => replaceByConstraint(pattern.asTerm, constraints)
      case None => expr

  def eval(fun: Abs): Result =
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
        case term @ Abs(properties, ident, tpe, expr) =>
          eval(expr, constraints) map { Abs(term)(properties, ident, tpe, _) }
        case term @ App(properties, expr, arg) =>
          evals(List(expr, arg), constraints) map { exprs => App(term)(properties, exprs.head, exprs.tail.head) }
        case term @ TypeAbs(ident, expr) =>
          eval(expr, constraints) map { TypeAbs(term)(ident, _) }
        case term @ TypeApp(expr, tpe) =>
          eval(expr, constraints) flatMap {
            case Reduction(TypeAbs(ident, expr), constraints) =>
              eval(subst(expr, Map(ident -> tpe)), constraints).reductions
            case Reduction(expr, constraints) =>
              List(Reduction(TypeApp(term)(expr, tpe), constraints))
          }
        case term @ Data(ctor, args) =>
          evals(args, constraints) map { args => Data(term)(ctor, args) }
        case term @ Var(_) =>
          Result(List(Reduction(term, constraints)))
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
