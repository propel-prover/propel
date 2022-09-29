package propel
package evaluator

import ast.*
import typer.*
import scala.annotation.targetName
import scala.collection.mutable

object Symbolic:
  case class Constraints private (pos: PatternConstraints, neg: Set[PatternConstraints]):
    def withPosConstraints(pos: PatternConstraints): Option[Constraints] =
      if pos forall { (expr, pattern) => this.pos.get(expr) contains pattern } then
        Some(this)
      else
        this.pos unify pos collect { case pos if !refutablePosNeg(pos, this.neg) => Constraints(pos, this.neg) }

    def withNegConstraints(neg: PatternConstraints)(using UniqueNaming): Option[(Constraints, PatternConstraints)] =
      withNegConstraints(Set(neg))

    def withNegConstraints(neg: Set[PatternConstraints])(using UniqueNaming): Option[(Constraints, PatternConstraints)] =
      if neg subsetOf this.neg then
        Some(this -> PatternConstraints.empty)
      else
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


  enum Control:
    case Continue
    case Stop
    case Terminate

  case class Configuration(
    normalize: (Term, Equalities) => Term = (expr, _) => expr,
    derive: Equalities => List[Equalities] = List(_),
    control: (Term, Equalities, Boolean) => (Term, Equalities, Control) = (expr, _, _) => (expr, Equalities.empty, Control.Continue))


  case class Result(reductions: List[Reduction]) extends AnyVal:
    def withConstraints(patternConstraints: PatternConstraints, config: Configuration = Configuration()) =
      Result(reductions flatMap { _.withConstraints(patternConstraints, config) })

  case class Reduction(expr: Term, constraints: Constraints, equalities: Equalities):
    def withConstraints(patternConstraints: PatternConstraints, config: Configuration = Configuration()) =
      constraints.withPosConstraints(patternConstraints) flatMap { constraints =>
        equalities.withEqualities(patternConstraints) map { equalities =>
          Reduction(normalize(expr, equalities, config, mutable.Map.empty), constraints, equalities)
        }
      }

  private case class Results(reductions: List[Reductions]) extends AnyVal

  private case class Reductions(exprs: List[Term], constraints: Constraints, equalities: Equalities)


  extension (results: Results)
    private inline def map(f: List[Term] => Term): Result = Result(results.reductions map { _ map f })

  extension (reductions: Reductions)
    private inline def map(f: List[Term] => Term): Reduction = Reduction(f(reductions.exprs), reductions.constraints, reductions.equalities)

  private def normalize(expr: Term, equalities: Equalities, config: Configuration, cache: mutable.Map[(Term, Equalities), Term]): Term =
    val term = substEqualities(expr, equalities)
    cache.getOrElseUpdate((term, equalities), config.normalize(term, equalities))

  private def normalize(equalities: Equalities, config: Configuration, cache: mutable.Map[(Term, Equalities), Term]): Option[Equalities] =
    def normalize(term: Term) =
      cache.getOrElseUpdate((term, equalities), config.normalize(term, equalities))

    val additional = (equalities.pos.toList map { (expr0, expr1) =>
      val normalized0 = normalize(expr0)
      val normalized1 = normalize(expr1)
      Option.when(expr0 != normalized0 || expr1 != normalized1)(normalized0 -> normalized1)
    }).flatten

    equalities.withEqualities(additional)

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

  private def constraintsFromEqualities(using UniqueNaming)(
      constraints: Option[Constraints],
      equalities: Option[Equalities]): Option[(Constraints, Equalities)] =
    constraints flatMap { constraints =>
      equalities flatMap { equalities =>
        constraints.withPosConstraints(equalities.posConstraints) flatMap { updated =>
          updated.withNegConstraints(equalities.negConstraints) flatMap { (updated, pos) =>
            if updated != constraints then
              constraintsFromEqualities(Some(updated), equalities.withEqualities(pos))
            else
              Some(constraints, equalities)
          }
        }
      }
    }


  def eval(expr: UniqueNames[Term | Result]): UniqueNames[Result] = expr linked {
    case expr: Term => eval(Result(List(Reduction(expr, Constraints.empty, Equalities.empty))), Configuration(), mutable.Map.empty, Control.Continue)
    case expr: Result => eval(expr, Configuration(), mutable.Map.empty, Control.Continue)
  }

  def eval(expr: UniqueNames[Term | Result], config: Configuration): UniqueNames[Result] = expr linked {
    case expr: Term => eval(Result(List(Reduction(expr, Constraints.empty, Equalities.empty))), config, mutable.Map.empty, Control.Continue)
    case expr: Result => eval(expr, config, mutable.Map.empty, Control.Continue)
  }

  def eval(expr: UniqueNames[Term], equalities: Equalities): UniqueNames[Result] =
    expr linked { expr => eval(Result(List(Reduction(expr, Constraints.empty, equalities))), Configuration(), mutable.Map.empty, Control.Continue) }

  def eval(expr: UniqueNames[Term], equalities: Equalities, config: Configuration): UniqueNames[Result] =
    expr linked { expr => eval(Result(List(Reduction(expr, Constraints.empty, equalities))), config, mutable.Map.empty, Control.Continue) }

  private def eval(init: Result, config: Configuration, cache: mutable.Map[(Term, Equalities), Term], control: Control)(using UniqueNaming): Result =
    def evals(exprs: List[Term], constraints: Constraints, equalities: Equalities, control: Control): (Results, Control) =
      exprs.foldLeft(Results(List(Reductions(List.empty, constraints, equalities))) -> control) { case ((results, control), expr) =>
        val reductions -> reductionsControl = results.reductions.foldLeft[(List[Reductions], Control)](List.empty -> control) {
          case ((reductions, control), Reductions(exprs, constraints, equalities)) =>
            val result -> resultControl = eval(expr, constraints, equalities, control, nested = true) 
            val resultReductions = result.reductions map { case Reduction(expr, constraints, equalities) =>
              Reductions(exprs :+ expr, constraints, equalities)
            }
            reductions ++ resultReductions -> resultControl
        }
        Results(reductions) -> reductionsControl
      }

    def eval(expr: Term, constraints: Constraints, equalities: Equalities, control: Control, nested: Boolean): (Result, Control) =
      if control != Control.Continue then
        Result(List(Reduction(expr, constraints, equalities))) -> control
      else
        val (term, equals, control) = config.control(replaceByEqualities(expr, equalities), equalities, nested)
        val normalized =
          if equals.pos.isEmpty && equals.neg.isEmpty then Some(constraints, equalities)
          else constraintsFromEqualities(Some(constraints), equalities.withEqualities(equals) flatMap { normalize(_, config, cache) })

        (term, control, normalized) match
          case (_, _, None) =>
            Result(List.empty) -> control

          case (_, Control.Terminate, Some(constraints, equalities)) =>
            Result(List(Reduction(term, constraints, equalities))) -> Control.Terminate

          case (_, Control.Stop, Some(constraints, equalities)) =>
            Result(List(Reduction(term, constraints, equalities))) -> Control.Continue

          case (Abs(properties, ident, tpe, expr), _, Some(constraints, equalities)) =>
            Result(List(Reduction(term, constraints, equalities))) -> control

          case (App(properties, expr, arg), _, Some(constraints, equalities)) =>
            val results -> resultsControl = evals(List(expr, arg), constraints, equalities, control)
            (results map { exprs => App(term)(properties, exprs.head, exprs.tail.head) }) -> resultsControl

          case (TypeAbs(ident, expr), _, Some(constraints, equalities)) =>
            Result(List(Reduction(term, constraints, equalities))) -> control

          case (TypeApp(expr, tpe), _, Some(constraints, equalities)) =>
            val result -> resultControl = eval(expr, constraints, equalities, control, nested = true)
            val reductions -> reductionsControl = result.reductions.foldLeft[(List[Reduction], Control)](List.empty -> resultControl) {
              case ((reductions, control), Reduction(TypeAbs(ident, expr), constraints, equalities)) =>
                val result -> resultControl = eval(subst(expr, Map(ident -> tpe)), constraints, equalities, control, nested)
                reductions ++ result.reductions -> resultControl
              case ((reductions, control), Reduction(expr, constraints, equalities)) =>
                (reductions :+ Reduction(TypeApp(term)(expr, tpe), constraints, equalities)) -> control
            }
            Result(reductions) -> reductionsControl

          case (Data(ctor, args), _, Some(constraints, equalities)) =>
            val results -> resultsControl = evals(args, constraints, equalities, control)
            (results map { args => Data(term)(ctor, args) }) -> resultsControl

          case (Var(_), _, Some(constraints, equalities)) =>
            Result(List(Reduction(term, constraints, equalities))) -> control

          case (Cases(scrutinee, cases), _, Some(constraints, equalities)) =>
            val result -> resultControl = eval(scrutinee, constraints, equalities, control, nested = true)
            val reductions -> reductionsControl = result.reductions.foldLeft[(List[Reduction], Control)](List.empty -> resultControl) {
              case ((reductions, control), Reduction(scrutinee, constraints, equalities)) =>
                def process(
                    cases: List[(Pattern, Term)],
                    constraints: Constraints,
                    equalities: Equalities,
                    control: Control): (List[Reduction], Control) = cases match
                  case Nil => Nil -> control
                  case (pattern, expr) :: tail =>
                    Unification.unify(pattern, normalize(scrutinee, equalities, config, cache)) match
                      case Unification.Full(substs) =>
                        val result -> resultControl = eval(subst(expr, substs), constraints, equalities, control, nested)
                        result.reductions -> resultControl

                      case Unification.Irrefutable(substs, posConstraints) =>
                        val posReductions -> posResult = 
                          val consts = constraints.withPosConstraints(posConstraints)
                          val equals = equalities.withEqualities(posConstraints)

                          constraintsFromEqualities(consts, equals flatMap { normalize(_, config, cache) }) match
                            case Some(consts, equals) =>
                              config.derive(equals).foldLeft[(List[Reduction], Control)](List.empty -> control) {
                                case (result @ (reductions, control), equals) =>
                                  constraintsFromEqualities(Some(consts), normalize(equals, config, cache)) match
                                    case Some(consts, equals) =>
                                      val result -> resultControl = eval(subst(expr, substs), consts, equals, control, nested)
                                      reductions ++ result.reductions -> resultControl
                                    case _ =>
                                      result
                              }
                            case _ =>
                              List.empty -> control

                        val negReductions -> negResult =
                          val (consts, pos) = (constraints.withNegConstraints(posConstraints)
                            map { (consts, pos) => (Some(consts), Some(pos)) }
                            getOrElse (None, None))
                          val equals = pos flatMap { equalities.withEqualities(_) flatMap { _.withUnequalities(posConstraints) } }

                          constraintsFromEqualities(consts, equals flatMap { normalize(_, config, cache) }) match
                            case Some(consts, equals) =>
                              config.derive(equals).foldLeft[(List[Reduction], Control)](List.empty -> posResult) {
                                case (result @ (reductions, control), equals) =>
                                  constraintsFromEqualities(Some(consts), normalize(equals, config, cache)) match
                                    case Some(consts, equals) =>
                                      val processedReductions -> processedControl = process(tail, consts, equals, control)
                                      reductions ++ processedReductions -> processedControl
                                    case _ =>
                                      result
                              }
                            case _ =>
                              List.empty -> posResult

                        posReductions ++ negReductions -> negResult

                      case _ =>
                        process(tail, constraints, equalities, control)

                val processedReductions -> processedControl = process(cases, constraints, equalities, control)
                reductions ++ processedReductions -> processedControl
            }
            Result(reductions) -> reductionsControl

    Result(init.reductions flatMap { case Reduction(expr, constraints, equalities) =>
      constraintsFromEqualities(Some(constraints), normalize(equalities, config, cache)) match
        case (Some(constraints, equalities)) =>
          val normalized = normalize(expr, equalities, config, cache)
          val exprResult -> exprControl = eval(normalized, constraints, equalities, control, nested = false)
          exprResult.reductions flatMap { case reduction @ Reduction(expr, constraints, equalities) =>
            val normalized = normalize(expr, equalities, config, cache)
            if expr eq normalized then
              List(reduction)
            else
              val normalizedResult -> normalizedControl = eval(normalized, constraints, equalities, exprControl, nested = false)
              if normalizedResult.reductions.size == 1 && normalizedResult.reductions.head.expr == expr then
                List(reduction)
              else
                Symbolic.eval(normalizedResult, config, cache, normalizedControl).reductions
          }
        case _ =>
          List.empty
    })
  end eval
end Symbolic
