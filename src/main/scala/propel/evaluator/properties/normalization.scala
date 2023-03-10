package propel
package evaluator
package properties

import ast.*
import util.*

case class Normalization private (
    pattern: Term,
    result: Term,
    abstraction: Symbol,
    variables: Set[Symbol],
    reversible: Boolean)(
    reversed: Normalization | Null):
  private def binds(pattern: Pattern): Set[Symbol] = pattern match
    case Match(ctor, args) => (args flatMap binds).toSet
    case Bind(ident) => Set(ident)

  private def rename(term: Term, mapping: Map[Symbol, Set[Symbol]], bound: Set[Symbol]): (Term, Map[Symbol, Set[Symbol]]) = term match
    case Abs(properties, ident, tpe, expr) =>
      let(rename(expr, mapping, bound + ident)) { Abs(term)(properties, ident, tpe, _) -> _ }
    case App(properties, expr, arg) =>
      let(rename(expr, mapping, bound)) { (expr, mapping) =>
        let(rename(arg, mapping, bound)) { App(term)(properties, expr, _) -> _ }
      }
    case TypeAbs(ident, expr) =>
      let(rename(expr, mapping, bound)) { TypeAbs(term)(ident, _) -> _ }
    case TypeApp(expr, tpe) =>
      let(rename(expr, mapping, bound)) { TypeApp(term)(_, tpe) -> _ }
    case Data(ctor, args) =>
      val renamed = args.foldRight(List.empty[Term], mapping) {
        case (arg, (args, mapping)) =>
          let(rename(arg, mapping, bound)) { (arg, mapping) => (arg :: args) -> mapping }
      }
      let(renamed) { Data(term)(ctor, _) -> _ }
    case Var(ident) =>
      if bound contains ident then
        term -> mapping
      else
        val fresh = Naming.freshIdent(ident, mapping.values.toSet flatMap { _ map { _.name } })
        Var(term)(fresh) -> mapping.updatedWith(ident) { _ map { _ + fresh } orElse Some(Set(fresh)) }
    case Cases(scrutinee, cases) =>
      let(rename(scrutinee, mapping, bound)) { (scrutinee, mapping) =>
        val renamed = cases.foldRight(List.empty[(Pattern, Term)], mapping) {
          case (pattern -> expr, (cases, mapping)) =>
            let(rename(expr, mapping, bound ++ binds(pattern))) { (expr, mapping) => (pattern -> expr :: cases) -> mapping }
        }
        let(renamed) { Cases(term)(scrutinee, _) -> _ }
      }

  val reverse = Option.when(reversible) {
    if reversed == null then
      Normalization(result, pattern, abstraction, variables, reversible)(this)
    else
      reversed
  }

  val free =
    pattern.syntacticInfo.freeVars.keySet ++
    result.syntacticInfo.freeVars.keySet --
    variables -
    abstraction

  val checking =
    def mappingSubst(mapping: Map[Symbol, Set[Symbol]]) =
      mapping collect { case (original, renamed) if abstraction != original && !(free contains original) =>
        original -> Var(renamed.head)
      }

    def mappingAbstractions(mapping: Map[Symbol, Set[Symbol]]) =
      mapping.getOrElse(abstraction, Set.empty) + abstraction

    def mappingFree(mapping: Map[Symbol, Set[Symbol]]) =
      mapping.foldLeft((free map { free => free -> free}).toMap) { case (result, (original, renamed)) =>
        if free contains original then
          result ++ (renamed map { _ -> original })
        else
          result
      }

    def mappingVariables(mapping: Map[Symbol, Set[Symbol]]) =
      (mapping collect { case (original, renamed) if renamed.size > 1 && (variables contains original) =>
        renamed
      }).toList

    val (renamedPattern, patternMapping) = rename(pattern, Map.empty, Set.empty)

    val renamedResult = subst(result, mappingSubst(patternMapping))

    Normalization.Checking(
      renamedPattern.withSyntacticInfo,
      renamedResult.withSyntacticInfo,
      mappingAbstractions(patternMapping),
      mappingVariables(patternMapping),
      mappingFree(patternMapping))(
      this)
  end checking
end Normalization

object Normalization:
  def apply(pattern: Term, result: Term, abstraction: Symbol, variables: Set[Symbol], reversible: Boolean): Normalization =
    Normalization(pattern, result, abstraction, variables, reversible)(null)

  case class Checking private[Normalization] (
      pattern: Term,
      result: Term,
      abstraction: Set[Symbol],
      equivalents: List[Set[Symbol]],
      free: Map[Symbol, Symbol])(
      val normalization: Normalization):

    private trait FunctionEqualResult(
        freeSubsts: Option[Map[Symbol, Term]]) extends PropertyChecking.FunctionEqualResult:
      def prepare(ident0: Symbol, ident1: Symbol, expr: Term) =
        def expandCalls(term: Term): Term = term match
          case Abs(properties, ident, tpe, expr) =>
            Abs(term)(properties, ident, tpe, expandCalls(expr))
          case App(_, App(_, Var(ident), arg0), arg1) if abstraction contains ident =>
            subst(expr, Map(ident0 -> expandCalls(arg0), ident1 -> expandCalls(arg1)))
          case App(properties, expr, arg) =>
            App(term)(properties, expandCalls(expr), expandCalls(arg))
          case TypeAbs(ident, expr) =>
            TypeAbs(term)(ident, expandCalls(expr))
          case TypeApp(expr, tpe) =>
            TypeApp(term)(expandCalls(expr), tpe)
          case Data(ctor, args) =>
            Data(term)(ctor, args map expandCalls)
          case Var(ident) =>
            freeSubsts flatMap { _.get(ident) } getOrElse term
          case Cases(scrutinee, cases) =>
            Cases(term)(expandCalls(scrutinee), cases map { (pattern, expr) =>
              pattern -> expandCalls(expr)
            })
        Data(equalDataConstructor, List(expandCalls(normalization.pattern), expandCalls(normalization.result))) -> Equalities.empty

    private trait Normal(
        freeSubsts: Option[Map[Symbol, Term]],
        expr: Term,
        checkAbstraction: Set[Term] => Boolean,
        checkFree: Map[Symbol, List[Term]] => Boolean,
        ensureDecreasingArgsForBinaryAbstraction: Boolean) extends PropertyChecking.Normal:

      private val patternArguments = arguments(normalization.pattern)

      def normalize(ensureDecreasing: (Property, Term) => Boolean)(equalities: Equalities) = scala.Function.unlift { (term: Term) =>
        freeSubsts flatMap { freeSubsts =>
          Unification.unify(pattern, term) flatMap { (substs, substsReverse) =>
            def abstractionCheck = abstraction flatMap { substs.get(_) }

            def freeCheck = free.foldLeft(Map.empty[Symbol, List[Term]]) { case (mapping, (renamed, original)) =>
              mapping.updatedWith(original) {
                _ flatMap { exprs => substs.get(renamed) map { _ :: exprs } } orElse (substs.get(renamed) map { List(_) })
              }
            }

            def canApply =
              !ensureDecreasingArgsForBinaryAbstraction ||
              (patternArguments zip arguments(pattern) forall { case ((patternArg0, patternArg1), (substitutedArg0, substitutedArg1)) =>
                let(Weight(substEqualities(patternArg0, equalities)),
                    Weight(substEqualities(patternArg1, equalities)),
                    Weight(subst(substitutedArg0, substs)),
                    Weight(subst(substitutedArg1, substs))) { (patternArg0, patternArg1, substitutedArg0, substitutedArg1) =>
                  substitutedArg0 < patternArg0 ||
                  substitutedArg1 < patternArg1 ||
                  substitutedArg0 + substitutedArg1 < patternArg0 + patternArg1
                }
              })

            Option.when(
                substsReverse.isEmpty &&
                checkAbstraction(abstractionCheck) &&
                checkFree(freeCheck) &&
                valid(substs, equivalents) &&
                canApply) {
              subst(result, substs ++ freeSubsts ++ (abstraction map { _ -> expr }))
            }
          }
        }
      }

    private def arguments(term: Term): Set[(Term, Term)] = term match
      case Abs(properties, ident, tpe, expr) =>
        arguments(expr)
      case App(_, App(_, Var(ident), arg0), arg1) if abstraction contains ident =>
        arguments(arg0) ++ arguments(arg1) + (arg0 -> arg1)
      case App(properties, expr, arg) =>
        arguments(expr) ++ arguments(arg)
      case TypeAbs(ident, expr) =>
        arguments(expr)
      case TypeApp(expr, tpe) =>
        arguments(expr)
      case Data(ctor, args) =>
        (args flatMap arguments).toSet
      case Var(ident) =>
        Set.empty
      case Cases(scrutinee, cases) =>
        arguments(scrutinee) ++ (cases flatMap { (_, expr) => arguments(expr) })

    private def replaceByEqualities(expr: Term, equalities: Equalities): Term =
      equalities.pos.get(expr) match
        case Some(expr) => replaceByEqualities(expr, equalities)
        case None => expr

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

    private def substs(freeExpr: Map[Symbol, Term]) =
      Option.when(free.values forall { freeExpr contains _}) {
        free map { (renamed, original) => renamed -> freeExpr(original) }
      }

    def apply(freeExpr: Map[Symbol, Term])
    : PropertyChecking.FunctionEqualResult =
      val freeSubsts = substs(freeExpr)
      new FunctionEqualResult(freeSubsts) { }

    def apply(
      expr: Term,
      checkAbstraction: Set[Term] => Boolean,
      checkFree: Map[Symbol, List[Term]] => Boolean,
      freeExpr: Map[Symbol, Term],
      ensureDecreasingArgsForBinaryAbstraction: Boolean)
    : PropertyChecking.FunctionEqualResult with PropertyChecking.Normal =
      val freeSubsts = substs(freeExpr)
      new FunctionEqualResult(freeSubsts) with Normal(freeSubsts, expr, checkAbstraction, checkFree, ensureDecreasingArgsForBinaryAbstraction) { }

    def apply(
      expr: Option[Term],
      checkAbstraction: Set[Term] => Boolean,
      checkFree: Map[Symbol, List[Term]] => Boolean,
      freeExpr: Map[Symbol, Term],
      ensureDecreasingArgsForBinaryAbstraction: Boolean)
    : (PropertyChecking.FunctionEqualResult, Option[PropertyChecking.Normal])=
      expr match
        case Some(expr) =>
          val checking = apply(expr, checkAbstraction, checkFree, freeExpr, ensureDecreasingArgsForBinaryAbstraction)
          (checking, Some(checking))
        case _ =>
          (apply(freeExpr), None)
  end Checking

  private def valid(substs: TermSubstitutions, equivalents: List[Set[Symbol]]) =
    equivalents forall { equivalents =>
      (equivalents flatMap { substs get _ }).size == 1
    }

  def specializationForSameAbstraction(special: Normalization, general: Normalization): Boolean =
    def specialization(special: Normalization.Checking, general: Normalization.Checking, specialExpr: Term, generalExpr: Term) =
      Unification.unify(generalExpr, specialExpr) filter { (generalConstraints, specialConstraints) =>
        specialConstraints.isEmpty &&
        (general.abstraction forall { ident =>
          generalConstraints.get(ident) collect { case Var(ident) => ident } forall { special.abstraction contains _ }
        })
      }

    specialization(special.checking, general.checking, special.checking.pattern, general.checking.pattern) exists { (substs, _) =>
      special.checking.result == subst(general.checking.result, substs)
    }
  end specializationForSameAbstraction

  def specializationForSameAbstraction(special: Normalization, general: Iterable[Normalization]): Boolean =
    general exists { specializationForSameAbstraction(special, _) }

  def equivalentForSameAbstraction(normalization0: Normalization, normalization1: Normalization): Boolean =
    normalization0 == normalization1 ||
    specializationForSameAbstraction(normalization0, normalization1) &&
    specializationForSameAbstraction(normalization1, normalization0)

  def distinct(normalizations: List[Normalization]): List[Normalization] = normalizations match
    case Nil => Nil
    case head :: tail =>
      def distinctTail(normalizations: List[Normalization]): List[Normalization] = normalizations match
        case Nil => Nil
        case tailHead :: tailTail =>
          if Normalization.equivalentForSameAbstraction(tailHead, head) then
            distinctTail(tailTail)
          else
            tailHead :: distinctTail(tailTail)
      head :: distinct(distinctTail(tail))
end Normalization
