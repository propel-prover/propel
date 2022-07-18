package propel
package ast

import util.*
import scala.collection.mutable

object AlphaConversion:
  case class UniqueNames private[AlphaConversion] (expr: Term)(using Names):
    def map[T](f: Names ?=> Term => T) = f(expr)

  class Names private[AlphaConversion] (private[AlphaConversion] val used: mutable.Set[String])

  sealed trait PotentialNames[R <: UniqueNames | Term](using val names: Names):
    inline def used = names.used
    def makeResult(expr: Term): R

  sealed trait PotentialNamesFallback:
    given[CompileToDef]: PotentialNames[UniqueNames](using Names(mutable.Set.empty)) with
      def makeResult(expr: Term) = UniqueNames(expr)

  object PotentialNames extends PotentialNamesFallback:
    given(using Names): PotentialNames[Term] with
      def makeResult(expr: Term) = expr

  def uniqueNames[R <: UniqueNames | Term](expr: Term)(using names: PotentialNames[R]): R =
    def renamePattern(pattern: Pattern): (Pattern, Map[Symbol, Symbol]) = pattern match
      case Match(ctor, args) =>
        let(args.map(renamePattern).unzip) { (args, substs) =>
          Match(pattern)(ctor, args) -> substs.fold(Map.empty) { _ ++ _ }
        }
      case Bind(ident) =>
        val fresh = Util.freshIdent(ident, names.used)
        names.used += fresh.name
        Bind(pattern)(fresh) -> Map(ident -> fresh)

    def renameTerm(term: Term, subst: Map[Symbol, Symbol]): Term = term match
      case Abs(properties, ident, expr) =>
        val fresh = Util.freshIdent(ident, names.used)
        names.used += fresh.name
        Abs(term)(properties, fresh, renameTerm(expr, subst + (ident -> fresh)))
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

    names.makeResult(renameTerm(expr, Map.empty))
end AlphaConversion
