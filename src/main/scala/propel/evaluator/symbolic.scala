package propel
package evaluator

import ast.*
import typer.*
import scala.annotation.targetName

object Symbolic:
  case class Constraints private (pos: PatternConstraints, neg: Set[PatternConstraints]):
    def withPosConstraints(pos: PatternConstraints): Option[Constraints] =
      this.pos unify pos collect { case pos if !refutablePosNeg(pos, this.neg) => Constraints(pos, this.neg) }

    def withNegConstraints(neg: PatternConstraints)(using UniqueNaming): Option[(Constraints, PatternConstraints)] =
      withNegConstraints(Set(neg))

    def withNegConstraints(neg: Set[PatternConstraints])(using UniqueNaming): Option[(Constraints, PatternConstraints)] =
      val negConstraints = this.neg ++ neg
      refutablePosFromNegTyped(negConstraints) flatMap { pos =>
        if pos.nonEmpty then
          Constraints(this.pos, negConstraints).withPosConstraints(pos) map { _ -> pos }
        else
          Option.when(!refutablePosNeg(this.pos, neg))(Constraints(this.pos, negConstraints) -> pos)
      }

    private def refutablePosNeg(pos: PatternConstraints, neg: Set[PatternConstraints]) =
      neg exists {
        _ forall { (negExpr, negPattern) =>
          pos.get(negExpr) exists { !Unification.refutable(negPattern, _) }
        }
      }

    private def refutablePosFromNegTyped(neg: Set[PatternConstraints])(using UniqueNaming) =
      val negTermConstraints = neg.foldLeft(List(Map.empty[Term, List[Pattern]])) { (negTermConstraints, neg) =>
        (neg flatMap { (expr, pattern) =>
          negTermConstraints map { _.updatedWith(expr) { _ map { pattern :: _ } orElse Some(List(pattern)) } }
        }).toList
      }

      val posTermConstraints = negTermConstraints map {
        _ map { (negExpr, negPatterns) =>
          negExpr.termType map { tpe =>
            negExpr -> patterns(negPatterns.foldLeft(tpe) { (tpe, pattern) => diff(tpe, pattern) getOrElse tpe })
          }
        }
      }

      Option.when(posTermConstraints exists { _ forall { _ forall { (_, patterns) => patterns.nonEmpty } } }) {
        posTermConstraints filter { _ forall { _ exists { (_, patterns) => patterns.size == 1 } } } match
          case List(pos) =>
            val constraints = PatternConstraints.make(pos flatMap { pos =>
              val (expr, List(pattern)) = pos.get
              val base = expr match
                case Var(ident) => ident.name
                case _ => "v"
              Option.when(this.pos.get(expr) forall { Unification.refutable(pattern, _) })(expr -> uniqueNames(base, pattern))
            })
            constraints getOrElse PatternConstraints.empty
          case _ =>
            PatternConstraints.empty
      }

    private def uniqueNames(base: String, pattern: Pattern)(using UniqueNaming): Pattern = pattern match
      case Match(ctor, args) => Match(pattern)(ctor, args map { uniqueNames(base, _) })
      case Bind(_) => Bind(pattern)(Symbol(UniqueNames.freshIdent(base)))
  end Constraints

  object Constraints:
    def empty = Constraints(PatternConstraints.empty, Set.empty)


  case class Configuration(
    normalize: (Term, Equalities) => Term = (expr, _) => expr,
    derive: Equalities => Option[Equalities] = Some(_))


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

  private def normalize(expr: Term, equalities: Equalities, config: Configuration): Term =
    config.normalize(expr, equalities) match
      case term @ Abs(properties, ident, tpe, expr) =>
        Abs(term)(properties, ident, tpe, normalize(expr, equalities, config))
      case term @ App(properties, expr, arg) =>
        App(term)(properties, normalize(expr, equalities, config), normalize(arg, equalities, config))
      case term @ TypeAbs(ident, expr) =>
        TypeAbs(term)(ident, normalize(expr, equalities, config))
      case term @ TypeApp(expr, tpe) =>
        TypeApp(term)(normalize(expr, equalities, config), tpe)
      case term @ Data(ctor, args) =>
        Data(term)(ctor, args map { normalize(_, equalities, config) })
      case term @ Var(_) =>
        term
      case term @ Cases(scrutinee, cases) =>
        Cases(term)(normalize(scrutinee, equalities, config), cases map { (pattern, expr) =>
          pattern -> normalize(expr, equalities, config)
        })

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
        Cases(term)(substEqualities(scrutinee, equalities), cases map { (pattern, expr) =>
          pattern -> substEqualities(expr, equalities)
        })

  private def replaceByEqualities(expr: Term, equalities: Equalities): Term =
    equalities.pos.get(expr) match
      case Some(expr) => replaceByEqualities(expr, equalities)
      case None => expr


  def eval(expr: UniqueNames[Term | Result]): UniqueNames[Result] = expr linked {
    case expr: Term => eval(Result(List(Reduction(expr, Constraints.empty, Equalities.empty))), Configuration())
    case expr: Result => eval(expr, Configuration())
  }

  def eval(expr: UniqueNames[Term | Result], config: Configuration): UniqueNames[Result] = expr linked {
    case expr: Term => eval(Result(List(Reduction(expr, Constraints.empty, Equalities.empty))), config)
    case expr: Result => eval(expr, config)
  }

  def eval(expr: UniqueNames[Term], equalities: Equalities): UniqueNames[Result] =
    expr linked { expr => eval(Result(List(Reduction(expr, Constraints.empty, equalities))), Configuration()) }

  def eval(expr: UniqueNames[Term], equalities: Equalities, config: Configuration): UniqueNames[Result] =
    expr linked { expr => eval(Result(List(Reduction(expr, Constraints.empty, equalities))), config) }

  private def eval(init: Result, config: Configuration)(using UniqueNaming): Result =
    def evals(exprs: List[Term], constraints: Constraints, equalities: Equalities): Results =
      exprs.foldLeft(Results(List(Reductions(List.empty, constraints, equalities)))) { (results, expr) =>
        results flatMap { case Reductions(exprs, constraints, equalities) =>
          eval(expr, constraints, equalities).reductions map { case Reduction(expr, constraints, equalities) =>
            Reductions(exprs :+ expr, constraints, equalities)
          }
        }
      }

    def eval(expr: Term, constraints: Constraints, equalities: Equalities): Result =
      config.normalize(replaceByEqualities(expr, equalities), equalities) match
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
                    val equals = equalities.withEqualities(posConstraints) flatMap config.derive
                    (consts, equals) match
                      case (Some(consts), Some(equals)) =>
                        eval(subst(expr, substs), consts, equals).reductions ++ {
                          val consts = constraints.withNegConstraints(posConstraints)
                          val equals = consts flatMap { (_, pos) =>
                            equalities.withEqualities(pos) flatMap { _.withUnequalities(posConstraints) }
                          }
                          (consts, equals) match
                            case (Some((consts, _)), Some(equals)) => process(tail, consts, equals)
                            case _ => List.empty
                        }
                      case _ =>
                        process(tail, constraints, equalities)

                  case _ =>
                    process(tail, constraints, equalities)

            process(cases, constraints, equalities)
          }

    Result(init.reductions flatMap { case Reduction(expr, constraints, equalities) =>
      eval(expr, constraints, equalities).reductions flatMap { case reduction @ Reduction(expr, constraints, equalities) =>
        val normalized = normalize(substEqualities(expr, equalities), equalities, config)
        if expr eq normalized then
          List(reduction)
        else
          val result = eval(normalized, constraints, equalities)
          if result.reductions.size == 1 && result.reductions.head.expr == expr then
            List(reduction)
          else
            Symbolic.eval(result, config).reductions
      }
    })
  end eval
end Symbolic
