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
        this.pos `unify` pos collect { case pos if !refutablePosNeg(pos, this.neg) => Constraints(pos, this.neg) }

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
        posTermConstraints filter { _ forall { _ exists { (_, patterns) => patterns.sizeIs == 1 } } } match
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
    select: (Term, Equalities) => List[(Term, Equalities)] = (_, _) => List.empty,
    derive: Equalities => List[Equalities] = List(_),
    control: (Term, Equalities, Boolean) => (Term, Equalities, Control) = (expr, _, _) => (expr, Equalities.empty, Control.Continue))


  case class Result(reductions: List[Reduction]) extends AnyVal:
    def withConstraints(patternConstraints: PatternConstraints, config: Configuration = Configuration())(using UniqueNaming) =
      Result(reductions flatMap { _.withConstraints(patternConstraints, config) })

  case class Reduction(expr: Term, constraints: Constraints, equalities: Equalities):
    def withConstraints(patternConstraints: PatternConstraints, config: Configuration = Configuration())(using UniqueNaming) =
      constraints.withPosConstraints(patternConstraints) flatMap { constraints =>
        equalities.withEqualities(patternConstraints) map { equalities =>
          Reduction(normalize(expr, equalities, config, mutable.Map.empty), constraints, equalities)
        }
      }

  private case class Results(reductions: List[Reductions]) extends AnyVal

  private case class Reductions(exprs: List[Term], constraints: Constraints, equalities: Equalities)


  extension (results: Results)
    private inline def map(f: List[Term] => Term): Result = Result(results.reductions map { _ `map` f })

  extension (reductions: Reductions)
    private inline def map(f: List[Term] => Term): Reduction = Reduction(f(reductions.exprs), reductions.constraints, reductions.equalities)

  private def normalize(expr: Term, equalities: Equalities, config: Configuration, cache: mutable.Map[(Term, Equalities), Term])(using UniqueNaming): Term =
    val term = substEqualities(expr, equalities)
    val normalized = cache.getOrElseUpdate((term, equalities), config.normalize(term, equalities))
    if term != normalized then UniqueNames.convert(normalized) else normalized

  private def derive(equalities: Equalities, config: Configuration, cache: mutable.Map[Equalities, List[Equalities]]) =
    cache.getOrElseUpdate(equalities, config.derive(equalities))

  private def substEqualities(expr: Term, equalities: Equalities)(using UniqueNaming): Term =
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

  private def replaceByEqualities(expr: Term, equalities: Equalities)(using UniqueNaming): Term =
    equalities.pos.get(UniformNames.convert(expr)) match
      case Some(expr) => replaceByEqualities(UniqueNames.convert(expr), equalities)
      case None => expr

  private def constraintsFromEqualities(using UniqueNaming)(
      constraints: Constraints,
      equalities: Equalities,
      cache: mutable.Map[(Constraints, Equalities), Option[(Constraints, Equalities)]]): Option[(Constraints, Equalities)] =
    cache.getOrElseUpdate(
      constraints -> equalities,
      constraints.withPosConstraints(equalities.posConstraints) flatMap { updated =>
        updated.withNegConstraints(equalities.negConstraints) flatMap { (updated, pos) =>
          if updated != constraints then
            equalities.withEqualities(pos) flatMap { constraintsFromEqualities(updated, _, cache) }
          else
            Some(constraints, equalities)
        }
      })

  private def substUniqueNames(expr: Term, substs: TermSubstitutions)(using UniqueNaming): Term =
    def prepareSubst(term: Term, names: Set[String], idents: Map[Symbol, List[Symbol]]): (Term, Set[String], Map[Symbol, List[Symbol]]) =
      term match
        case Abs(properties, ident, tpe, expr) =>
          val (exprSubst, exprNames, exprIdents) = prepareSubst(expr, names, idents)
          (Abs(term)(properties, ident, tpe, exprSubst), exprNames, exprIdents)
        case App(properties, expr, arg) =>
          val (exprSubst, exprNames, exprIdents) = prepareSubst(expr, names, idents)
          val (argSubst, argNames, argIdents) = prepareSubst(arg, exprNames, exprIdents)
          (App(term)(properties, exprSubst, argSubst), argNames, argIdents)
        case TypeAbs(ident, expr) =>
          val (exprSubst, exprNames, exprIdents) = prepareSubst(expr, names, idents)
          (TypeAbs(term)(ident, exprSubst), exprNames, exprIdents)
        case TypeApp(expr, tpe) =>
          val (exprSubst, exprNames, exprIdents) = prepareSubst(expr, names, idents)
          (TypeApp(term)(exprSubst, tpe), exprNames, exprIdents)
        case Data(ctor, args) =>
          val (argsSubst, argsNames, argsIdents) =
            args.foldRight[(List[Term], Set[String], Map[Symbol, List[Symbol]])](List.empty, names, idents) {
              case (arg, (args, names, idents)) =>
                val (argSubst, argNames, argIdents) = prepareSubst(arg, names, idents)
                ((argSubst :: args), argNames, argIdents)
            }
          (Data(term)(ctor, argsSubst), argsNames, argsIdents)
        case Var(ident) =>
          if substs contains ident then
            val fresh = Naming.freshIdent(Symbol("□"), names)
            (Var(fresh), names + fresh.name, idents.updatedWith(ident) { _ map { fresh :: _ } orElse Some(List(fresh)) })
          else
            (term, names, idents)
        case Cases(scrutinee, cases) =>
          val (scrutineeSubst, scrutineeNames, scrutineeIdents) = prepareSubst(scrutinee, names, idents)
          val (casesSubst, casesNames, casesIdents) =
            cases.foldRight[(List[(Pattern, Term)], Set[String], Map[Symbol, List[Symbol]])](List.empty, scrutineeNames, scrutineeIdents) {
              case (pattern -> expr, (cases, names, idents)) =>
                val (exprSubst, exprNames, exprIdents) = prepareSubst(expr, names, idents)
                (((pattern -> exprSubst) :: cases), exprNames, exprIdents)
            }
          (Cases(term)(scrutineeSubst, casesSubst), casesNames, casesIdents)

    val (term, info) = expr.syntactic

    if substs.keys exists { info.freeVars.getOrElse(_, 0) > 1 } then
      val (substTerm, _, substIdents) = prepareSubst(term, UniqueNames.usedNames.toSet, Map.empty)
      val substSubsts = substIdents flatMap { (ident, idents) =>
        val expr = substs(ident)
        (idents.head -> expr) :: (idents.tail map { _ -> UniqueNames.convert(expr) })
      }
      subst(substTerm, substSubsts)
    else if substs.keys exists { info.freeVars.getOrElse(_, 0) > 0 } then
      subst(term, substs)
    else
      term
  end substUniqueNames


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

  private enum Mode:
    case CaseAnalysis
    case PartialEvaluation

  private def eval(
      init: Result,
      config: Configuration,
      exprCache: mutable.Map[(Term, Equalities), Term] = mutable.Map.empty,
      equalsCache: mutable.Map[Equalities, List[Equalities]] = mutable.Map.empty,
      constsCache: mutable.Map[(Constraints, Equalities), Option[(Constraints, Equalities)]] = mutable.Map.empty,
      evalCache: mutable.Map[(Term, Constraints, Equalities, Mode), Option[Result]] = mutable.Map.empty,
      control: Control = Control.Continue)(using UniqueNaming): Result =
    def evalEqualities(constraints: Constraints, equalities: Equalities, control: Control, processed: mutable.Set[Equalities])(using UniqueNaming): (List[Equalities], Control) =
      val maxBit = 8
      val max = 1 << maxBit

      def normalizeExpression(term: Term) =
        val normalized = exprCache.getOrElseUpdate((term, equalities), config.normalize(term, equalities))
        if term != normalized then UniqueNames.convert(normalized) else normalized

      def evalExpression(term: Term, constraints: Constraints, equalities: Equalities, control: Control) =
        val normalized = normalizeExpression(term)
        eval(normalized, constraints, equalities, control, nested = true, mode = Mode.PartialEvaluation) match
          case Result(List(Reduction(expr, _, _))) -> control if control != Control.Terminate =>
            val result -> resultControl = eval(expr, constraints, equalities, control, nested = true, mode = Mode.CaseAnalysis)
            (result, resultControl, expr)
          case _ -> control =>
            (Result(List.empty), control, normalized)

      def evaluateEqualities(pos: Map[Term, Term]) = pos.foldLeft(List(equalities) -> control) {
        case (evaluatedEqualities @ (List() -> _), _) =>
          evaluatedEqualities
        case (evaluatedEqualities -> control, exprs @ (expr0, expr1)) if (evaluatedEqualities map { _.pos.size }).sum < max =>
          val reducedEqualities = equalities.withoutEqualities(exprs)

          val (result0, control0, normalized0) = evalExpression(expr0, constraints, reducedEqualities, control)
          val (result1, control1, normalized1) = evalExpression(expr1, constraints, reducedEqualities, control)

          def equivalentReduction(reduction: Reduction, expr: Term) =
            reduction.expr == expr && reduction.equalities.withoutEqualities(exprs) == reducedEqualities

          if control0 == Control.Terminate || control1 == Control.Terminate then
            List.empty -> Control.Terminate
          if result0.reductions.isEmpty || result1.reductions.isEmpty then
            List.empty -> control
          else if result0.reductions.sizeIs == 1 &&
                  result1.reductions.sizeIs == 1 &&
                  equivalentReduction(result0.reductions.head, expr0) &&
                  equivalentReduction(result1.reductions.head, expr1) then
            evaluatedEqualities -> control
          else
            (result0.reductions flatMap { case Reduction(expr0, _, equalities0) =>
              result1.reductions flatMap { case Reduction(expr1, _, equalities1) =>
                evaluatedEqualities flatMap { equalities =>
                  equalities.withEqualities(equalities0.pos ++ equalities1.pos + (expr0 -> expr1) + (normalized0 -> normalized1))
                }
              }
            }) -> control
        case (evaluatedEqualities, _) =>
          evaluatedEqualities
      }

      val (pos, posExtended) = equalities.posExpanded

      val (evaluated, evaluatedControl) = evaluateEqualities(pos)

      val evaluatedDerived = evaluated flatMap config.derive

      val (evaluatedExtended, evaluatedControlExtended) =
        if evaluatedDerived.nonEmpty then
          evaluateEqualities(posExtended)
        else
          List.empty -> evaluatedControl

      val evaluatedExtendedDerived = evaluatedExtended flatMap config.derive

      if evaluatedExtendedDerived.nonEmpty then
        if evaluatedDerived.sizeIs > 1 || evaluatedDerived.sizeIs == 1 && evaluatedDerived.head != equalities then
          val unprocessed = evaluatedDerived filterNot { processed contains _ }
          processed ++= unprocessed

          if unprocessed.sizeIs > 1 || unprocessed.sizeIs == 1 && unprocessed.head != equalities then
            val evaluatedEqualities -> evaluatedControl =
              unprocessed.tail.foldLeft(evalEqualities(constraints, unprocessed.head, control, processed)) {
                case (combinedEqualities @ (List() -> _), _) =>
                  combinedEqualities
                case (combinedEqualities, equalities) if processed contains equalities =>
                  combinedEqualities
                case ((combinedEqualities, control), equalities) =>
                  val evaluatedEqualities -> evaluatedControl = evalEqualities(constraints, equalities, control, processed)
                  if evaluatedEqualities.nonEmpty then
                    (combinedEqualities ++ evaluatedEqualities) -> evaluatedControl
                  else
                    List.empty -> evaluatedControl
              }
            evaluatedEqualities.distinct -> evaluatedControl
          else
            evaluatedDerived -> evaluatedControlExtended
        else
          evaluatedDerived -> evaluatedControlExtended
      else
        List.empty -> evaluatedControlExtended
    end evalEqualities

    def evals(exprs: List[Term], constraints: Constraints, equalities: Equalities, control: Control, mode: Mode): (Results, Control) =
      exprs.foldLeft(Results(List(Reductions(List.empty, constraints, equalities))) -> control) { case ((results, control), expr) =>
        val reductions -> reductionsControl = results.reductions.foldLeft[(List[Reductions], Control)](List.empty -> control) {
          case (result @ (_, Control.Terminate), _) =>
            result
          case ((reductions, control), Reductions(exprs, constraints, equalities)) =>
            val result -> resultControl = eval(expr, constraints, equalities, control, nested = true, mode)
            val resultReductions = result.reductions map { case Reduction(expr, constraints, equalities) =>
              Reductions(exprs :+ expr, constraints, equalities)
            }
            reductions ++ resultReductions -> resultControl
        }
        Results(reductions) -> reductionsControl
      }
    end evals

    def eval(expr: Term, constraints: Constraints, equalities: Equalities, control: Control, nested: Boolean, mode: Mode): (Result, Control) =
      def makeResult(reductions: List[Reduction]) =
        val result = Result(reductions)
        evalCache += (expr, constraints, equalities, mode) -> Some(result)
        result

      evalCache get (expr, constraints, equalities, mode) match
        case Some(Some(result)) => return result -> control
        case Some(_) => return Result(List(Reduction(expr, constraints, equalities))) -> control
        case _ => evalCache += (expr, constraints, equalities, mode) -> None

      if control != Control.Continue then
        makeResult(List(Reduction(expr, constraints, equalities))) -> control
      else
        val selections = config.select(expr, equalities)
        val selectionsReductions -> selectionsControl =
          selections.foldLeft[(List[Reduction], Control)](List.empty -> control) {
            case (result @ (_, Control.Terminate), _) =>
              result
            case ((reductions, control), (expr, equals)) =>
              val exprResult -> exprControl =
                (equalities.withEqualities(equals) flatMap { constraintsFromEqualities(constraints, _, constsCache) }) match
                  case Some(consts, equals) => eval(expr, consts, equals, control, nested, mode)
                  case _ => Result(List.empty) -> control
              reductions ++ exprResult.reductions -> exprControl
          }

        if selections.nonEmpty && (mode != Mode.PartialEvaluation || selectionsReductions.sizeIs <= 1) then
          makeResult(selectionsReductions) -> selectionsControl
        else
          val (term, equals, control) = config.control(replaceByEqualities(expr, equalities), equalities, nested)
          val normalized =
            if equals.pos.isEmpty && equals.neg.isEmpty then Some(constraints, equalities)
            else equalities.withEqualities(equals) flatMap { constraintsFromEqualities(constraints, _, constsCache) }

          (term, control, normalized) match
            case (_, _, None) =>
              makeResult(List.empty) -> control

            case (_, Control.Terminate, Some(constraints, equalities)) =>
              makeResult(List(Reduction(term, constraints, equalities))) -> Control.Terminate

            case (_, Control.Stop, Some(constraints, equalities)) =>
              makeResult(List(Reduction(term, constraints, equalities))) -> Control.Continue

            case (Abs(properties, ident, tpe, expr), _, Some(constraints, equalities)) =>
              makeResult(List(Reduction(term, constraints, equalities))) -> control

            case (App(properties, expr, arg), _, Some(constraints, equalities)) =>
              val results -> resultsControl = evals(List(expr, arg), constraints, equalities, control, mode)
              val reductions -> reductionsControl = results.reductions.foldLeft[(List[Reduction], Control)](List.empty -> resultsControl) {
                case (results @ (_, Control.Terminate), _) =>
                  results
                case ((reductions, control), Reductions(List(expr, arg), constraints, equalities))
                    if equivalent(expr, arg) =>
                  (reductions :+ Reduction(App(term)(properties, expr, arg), constraints, equalities)) -> control
                case ((reductions, control), Reductions(List(expr @ Abs(_, _, _, App(_, expr0, expr1)), arg), constraints, equalities))
                    if equivalent(expr0, expr1) =>
                  (reductions :+ Reduction(App(term)(properties, expr, arg), constraints, equalities)) -> control
                case ((reductions, control), Reductions(List(Abs(_, ident, _, expr), arg), constraints, equalities)) =>
                  val result -> resultControl = eval(substUniqueNames(expr, Map(ident -> arg)), constraints, equalities, control, nested, mode)
                  reductions ++ result.reductions -> resultControl
                case ((reductions, control), Reductions(exprs, constraints, equalities)) =>
                  val List(expr, arg) = exprs
                  (reductions :+ Reduction(App(term)(properties, expr, arg), constraints, equalities)) -> control
              }
              if mode == Mode.PartialEvaluation && reductions.sizeIs > 1 then
                makeResult(List(Reduction(term, constraints, equalities))) -> control
              else
                makeResult(reductions) -> reductionsControl

            case (TypeAbs(ident, expr), _, Some(constraints, equalities)) =>
              makeResult(List(Reduction(term, constraints, equalities))) -> control

            case (TypeApp(expr, tpe), _, Some(constraints, equalities)) =>
              val result -> resultControl = eval(expr, constraints, equalities, control, nested = true, mode)
              val reductions -> reductionsControl = result.reductions.foldLeft[(List[Reduction], Control)](List.empty -> resultControl) {
                case (result @ (_, Control.Terminate), _) =>
                  result
                case ((reductions, control), Reduction(TypeAbs(ident, expr), constraints, equalities)) =>
                  val result -> resultControl = eval(subst(expr, Map(ident -> tpe)), constraints, equalities, control, nested, mode)
                  reductions ++ result.reductions -> resultControl
                case ((reductions, control), Reduction(expr, constraints, equalities)) =>
                  (reductions :+ Reduction(TypeApp(term)(expr, tpe), constraints, equalities)) -> control
              }
              if mode == Mode.PartialEvaluation && reductions.sizeIs > 1 then
                makeResult(List(Reduction(term, constraints, equalities))) -> control
              else
                makeResult(reductions) -> reductionsControl

            case (Data(ctor, args), _, Some(constraints, equalities)) =>
              val results -> resultsControl = evals(args, constraints, equalities, control, mode)
              if mode == Mode.PartialEvaluation && results.reductions.sizeIs > 1 then
                makeResult(List(Reduction(term, constraints, equalities))) -> control
              else
                makeResult(results.reductions map { _ map { args => Data(term)(ctor, args) } }) -> resultsControl

            case (Var(_), _, Some(constraints, equalities)) =>
              makeResult(List(Reduction(term, constraints, equalities))) -> control

            case (Cases(scrutinee, cases), _, Some(constraints, equalities)) =>
              val result -> resultControl = eval(scrutinee, constraints, equalities, control, nested = true, mode)
              val reductions -> reductionsControl = result.reductions.foldLeft[(List[Reduction], Control)](List.empty -> resultControl) {
                case (result @ (_, Control.Terminate), _) =>
                  result
                case ((reductions, control), Reduction(scrutinee, constraints, equalities)) =>
                  def process(
                      cases: List[(Pattern, Term)],
                      constraints: Constraints,
                      equalities: Equalities,
                      control: Control): (List[Reduction], Control) = cases match
                    case Nil => Nil -> control
                    case (pattern, expr) :: tail =>
                      Unification.unify(pattern, normalize(scrutinee, equalities, config, exprCache)) match
                        case Unification.Full(substs) =>
                          val result -> resultControl = eval(substUniqueNames(expr, substs), constraints, equalities, control, nested, mode)
                          result.reductions -> resultControl

                        case Unification.Irrefutable(substs, posConstraints) =>
                          val posReductions -> posResult =
                            constraints.withPosConstraints(posConstraints) match
                              case Some(consts) =>
                                val equals = equalities.withEqualities(posConstraints)

                                equals flatMap { constraintsFromEqualities(consts, _, constsCache) } match
                                  case Some(consts, equals) =>
                                    derive(equals, config, equalsCache).foldLeft[(List[Reduction], Control)](List.empty -> control) {
                                      case (result @ (_, Control.Terminate), _) =>
                                        result
                                      case (result @ (reductions, control), equals) =>
                                        constraintsFromEqualities(consts, equals, constsCache) match
                                          case Some(consts, equals) =>
                                            val result -> resultControl = eval(substUniqueNames(expr, substs), consts, equals, control, nested, mode)
                                            reductions ++ result.reductions -> resultControl
                                          case _ =>
                                            result
                                    }
                                  case _ =>
                                    List.empty -> control
                              case _ =>
                                List.empty -> control

                          val negReductions -> negResult =
                            constraints.withNegConstraints(posConstraints) match
                              case Some(consts, pos) =>
                                val equals = equalities.withEqualities(pos) flatMap { _.withUnequalities(posConstraints) }

                                equals flatMap { constraintsFromEqualities(consts, _, constsCache) } match
                                  case Some(consts, equals) =>
                                    derive(equals, config, equalsCache).foldLeft[(List[Reduction], Control)](List.empty -> posResult) {
                                      case (result @ (_, Control.Terminate), _) =>
                                        result
                                      case (result @ (reductions, control), equals) =>
                                        constraintsFromEqualities(consts, equals, constsCache) match
                                          case Some(consts, equals) =>
                                            val processedReductions -> processedControl = process(tail, consts, equals, control)
                                            reductions ++ processedReductions -> processedControl
                                          case _ =>
                                            result
                                    }
                                  case _ =>
                                    List.empty -> posResult
                              case _ =>
                                List.empty -> posResult

                          posReductions ++ negReductions -> negResult

                        case _ =>
                          process(tail, constraints, equalities, control)

                  val processedReductions -> processedControl = process(cases, constraints, equalities, control)
                  reductions ++ processedReductions -> processedControl
              }

              if mode == Mode.PartialEvaluation && reductions.sizeIs > 1 then
                if result.reductions.sizeIs > 1 then
                  makeResult(List(Reduction(term, constraints, equalities))) -> control
                else if result.reductions.sizeIs == 1 then
                  makeResult(List.empty) -> control
                else
                  val results -> resultsControl = evals(cases map { (_, expr) => expr }, result.reductions.head.constraints, result.reductions.head.equalities, control, mode)
                  if results.reductions.sizeIs > 1 then
                    makeResult(List(Reduction(term, constraints, equalities))) -> control
                  else
                    makeResult(results.reductions map {
                      _ map { exprs =>
                        Cases(term)(result.reductions.head.expr, cases zip exprs map { case ((pattern, _), expr) => pattern -> expr })
                      }
                    }) -> resultsControl
              else
                makeResult(reductions) -> reductionsControl
    end eval

    Result(init.reductions flatMap { case Reduction(expr, constraints, equalities) =>
      constraintsFromEqualities(constraints, equalities, constsCache) match
        case (Some(constraints, equalities)) =>
          val normalized = normalize(expr, equalities, config, exprCache)
          val exprResult -> exprControl = eval(normalized, constraints, equalities, control, nested = false, mode = Mode.CaseAnalysis)

          if exprControl != Control.Terminate then
            exprResult.reductions flatMap { case reduction @ Reduction(expr, constraints, equalities) =>
              val (evaluatedEqualities, evaluatedControl) = evalEqualities(constraints, equalities, exprControl, mutable.Set.empty)

              if evaluatedControl != Control.Terminate then
                evaluatedEqualities flatMap { equalities =>
                  val normalized = normalize(expr, equalities, config, exprCache)

                  if expr == normalized then
                    List(Reduction(expr, constraints, equalities))
                  else
                    val normalizedResult -> normalizedControl = eval(normalized, constraints, equalities, evaluatedControl, nested = false, mode = Mode.CaseAnalysis)
                    if normalizedResult.reductions.sizeIs == 1 && normalizedResult.reductions.head.expr == expr then
                      List(Reduction(expr, constraints, equalities))
                    else
                      Symbolic.eval(normalizedResult, config, exprCache, equalsCache, constsCache, evalCache, normalizedControl).reductions
                }
              else
                List(reduction)
            }
          else
            exprResult.reductions
        case _ =>
          List.empty
    })
  end eval
end Symbolic
