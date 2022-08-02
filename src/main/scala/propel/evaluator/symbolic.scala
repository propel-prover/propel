package propel
package evaluator

import ast.*
import typer.*
import scala.annotation.targetName

object Symbolic:
  case class Constraints private (pos: PatternConstraints, neg: Set[PatternConstraints]):
    def withPosConstraints(pos: PatternConstraints): Option[Constraints] =
      this.pos unify pos collect { case pos if !refutablePosNeg(pos, this.neg) => Constraints(pos, this.neg) }

    def withNegConstraints(neg: PatternConstraints): Option[Constraints] =
      withNegConstraints(Set(neg))

    def withNegConstraints(neg: Set[PatternConstraints]): Option[Constraints] =
      val negConstraints = this.neg ++ neg
      Option.when(!refutablePosNeg(this.pos, neg) && !refutableNegTyped(negConstraints))(Constraints(this.pos, negConstraints))

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
  end Constraints

  object Constraints:
    def empty = Constraints(PatternConstraints.empty, Set.empty)


  case class Result(reductions: List[Reduction]) extends AnyVal

  case class Reduction(expr: Term, constraints: Constraints, equalities: Equalities)

  private case class Results(reductions: List[Reductions]) extends AnyVal

  private case class Reductions(exprs: List[Term], constraints: Constraints, equalities: Equalities)


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
    private inline def map(f: List[Term] => Term): Reduction = Reduction(f(reductions.exprs), reductions.constraints, reductions.equalities)
    private inline def flatMap(f: Term => List[Term]): Reductions = reductions.copy(exprs = reductions.exprs flatMap f)

  private def substEqualities(expr: Term, equalities: Equalities): Term =
    replaceByEqualities(expr, equalities) match
      case term @ Abs(properties, ident, tpe, expr) =>
        Abs(term)(properties, ident, tpe, substEqualities(expr, equalities))
      case term @ App(properties, expr, arg) =>
        App(term)(properties, substEqualities(expr, equalities), substEqualities(arg, equalities))
      case term @ TypeAbs(ident, expr) =>
        TypeAbs(term)(ident, substEqualities(expr, equalities))
      case term @ TypeApp(expr, tpe) =>
        TypeApp(term)(substEqualities(expr, equalities), tpe)
      case term @ Data(ctor, args) =>
        Data(term)(ctor, args map { substEqualities(_, equalities) })
      case term @ Var(_) =>
        term
      case term @ Cases(scrutinee, cases) =>
        Cases(term)(substEqualities(scrutinee, equalities), cases map { (pattern, expr) => pattern -> substEqualities(expr, equalities) })

  private def replaceByEqualities(expr: Term, equalities: Equalities): Term =
    equalities.pos.get(expr) match
      case Some(expr) => replaceByEqualities(expr, equalities)
      case None => expr

  def eval(fun: Abs, equalities: Equalities = Equalities.empty): Result =
    def evals(exprs: List[Term], constraints: Constraints, equalities: Equalities): Results =
      exprs.foldLeft(Results(List(Reductions(List.empty, constraints, equalities)))) { (results, expr) =>
        results flatMap { case Reductions(exprs, constraints, equalities) =>
          eval(expr, constraints, equalities).reductions map { case Reduction(expr, constraints, equalities) =>
            Reductions(exprs :+ expr, constraints, equalities)
          }
        }
      }

    def eval(expr: Term, constraints: Constraints, equalities: Equalities): Result =
      replaceByEqualities(expr, equalities) match
        case term @ Abs(properties, ident, tpe, expr) =>
          eval(expr, constraints, equalities) map { Abs(term)(properties, ident, tpe, _) }
        case term @ App(properties, expr, arg) =>
          evals(List(expr, arg), constraints, equalities) map { exprs => App(term)(properties, exprs.head, exprs.tail.head) }
        case term @ TypeAbs(ident, expr) =>
          eval(expr, constraints, equalities) map { TypeAbs(term)(ident, _) }
        case term @ TypeApp(expr, tpe) =>
          eval(expr, constraints, equalities) flatMap {
            case Reduction(TypeAbs(ident, expr), constraints, equalities) =>
              eval(subst(expr, Map(ident -> tpe)), constraints, equalities).reductions
            case Reduction(expr, constraints, equalities) =>
              List(Reduction(TypeApp(term)(expr, tpe), constraints, equalities))
          }
        case term @ Data(ctor, args) =>
          evals(args, constraints, equalities) map { args => Data(term)(ctor, args) }
        case term @ Var(_) =>
          Result(List(Reduction(term, constraints, equalities)))
        case Cases(scrutinee, cases) =>
          eval(scrutinee, constraints, equalities) flatMap { case Reduction(scrutinee, constraints, equalities) =>
            def process(cases: List[(Pattern, Term)], constraints: Constraints, equalities: Equalities): List[Reduction] = cases match
              case Nil => Nil
              case (pattern, expr) :: tail =>
                Unification.unify(pattern, scrutinee) match
                  case Unification.Full(substs) =>
                    eval(subst(expr, substs), constraints, equalities).reductions

                  case Unification.Irrefutable(substs, posConstraints) =>
                    val consts = constraints.withPosConstraints(posConstraints)
                    val equals = equalities.withEqualities(posConstraints) flatMap properties.equalities.derive
                    (consts, equals) match
                      case (Some(consts), Some(equals)) =>
                        eval(subst(expr, substs), consts, equals).reductions ++ {
                          val consts = constraints.withNegConstraints(posConstraints)
                          val equals = equalities.withUnequalities(posConstraints)
                          (consts, equals) match
                            case (Some(consts), Some(equals)) => process(tail, consts, equals)
                            case _ => List.empty
                        }
                      case _ =>
                        process(tail, constraints, equalities)

                  case _ =>
                    process(tail, constraints, equalities)

            process(cases, constraints, equalities)
          }

    val result = eval(fun.expr, Constraints.empty, equalities)
    Result(result.reductions map { reduction => reduction map { substEqualities(_, reduction.equalities) } })
  end eval
end Symbolic
