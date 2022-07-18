package propel
package evaluator

import ast.*
import util.*
import scala.collection.mutable

object AlphaConversion:
  case class UniqueNames(expr: Term)(using NameSets):
    def map[T](f: NameSets ?=> Term => T) = f(expr)

  class NameSets private[AlphaConversion] (private[AlphaConversion] val used: mutable.Set[String])

  sealed trait PotentialNameSets[R <: UniqueNames | Term](using val sets: NameSets):
    inline def used = sets.used
    def makeResult(expr: Term): R

  sealed trait PotentialNameSetsFallback:
    given[CompileToDef]: PotentialNameSets[UniqueNames](using NameSets(mutable.Set.empty)) with
      def makeResult(expr: Term) = UniqueNames(expr)

  object PotentialNameSets extends PotentialNameSetsFallback:
    given(using NameSets): PotentialNameSets[Term] with
      def makeResult(expr: Term) = expr

  def uniqueNames[R <: UniqueNames | Term](expr: Term)(using sets: PotentialNameSets[R]): R =
    def freshIdent(base: Symbol): Symbol =
      def freshIdent(base: String, index: Int): String =
        val ident = base + Util.subscript(index)
        if sets.used.contains(ident) then
          freshIdent(base, index + 1)
        else
          sets.used += ident
          ident

      Symbol(freshIdent(Util.dropSubscript(base.name), 1))

    def renamePattern(pattern: Pattern): (Pattern, Map[Symbol, Symbol]) = pattern match
      case Match(ctor, args) =>
        let(args.map(renamePattern).unzip) { (args, substs) =>
          Match(pattern)(ctor, args) -> substs.fold(Map.empty) { _ ++ _ }
        }
      case Bind(ident) =>
        val fresh = freshIdent(ident)
        Bind(pattern)(fresh) -> Map(ident -> fresh)

    def renameTerm(term: Term, subst: Map[Symbol, Symbol]): Term = term match
      case Abs(properties, arg, expr) =>
        val fresh = freshIdent(arg)
        Abs(term)(properties, fresh, renameTerm(expr, subst + (arg -> fresh)))
      case App(properties, expr, arg) =>
        App(term)(properties, renameTerm(expr, subst), renameTerm(arg, subst))
      case Data(ctor, args) =>
        Data(term)(ctor, args map { renameTerm(_, subst) })
      case Var(ident) =>
        subst.get(ident) map { Var(_) } getOrElse term
      case Cases(scrutinee, cases) =>
        let(renameTerm(scrutinee, subst)) { scrutinee =>
          val renamedCases = cases map { (pattern, expr) =>
            let(renamePattern(pattern)) { (pattern, additionalSubst) =>
              pattern -> renameTerm(expr, subst ++ additionalSubst)
            }
          }
          Cases(term)(scrutinee, renamedCases)
        }

    sets.makeResult(renameTerm(expr, Map.empty))
end AlphaConversion
