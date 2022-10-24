package propel
package ast

import java.util.concurrent.ConcurrentHashMap
import scala.jdk.CollectionConverters._
import util.*

type UniqueNaming = UniqueNames.UniqueNaming

val UniqueNaming: UniqueNames.UniqueNaming.type = UniqueNames.UniqueNaming

case class UniqueNames[+T] private (wrapped: T)(using UniqueNaming):
  def linked[U](f: UniqueNaming ?=> T => U): UniqueNames[U] =
    UniqueNames(f(wrapped))
  def unlinked[U](f: UniqueNaming ?=> T => U): UniqueNames[U] =
    letgiven(UniqueNames.UniqueNaming(ConcurrentHashMap(summon.used))) { UniqueNames(f(wrapped)) }
  def unwrap[U](f: UniqueNaming.Immutable ?=> T => U): U =
    f(wrapped)

object UniqueNames:
  class UniqueNaming private[UniqueNames] (used: ConcurrentHashMap[String, Unit]) extends UniqueNaming.Immutable(used)

  object UniqueNaming:
    class Immutable private[UniqueNames] (private[UniqueNames] val used: ConcurrentHashMap[String, Unit])

  def apply[T](v: UniqueNaming ?=> T): UniqueNames[T] =
    given UniqueNaming(ConcurrentHashMap())
    UniqueNames(v)


  def usedNames(using UniqueNaming.Immutable): collection.Set[String] =
    summon.used.asScala.keySet


  private def freshIdent(base: String, used: ConcurrentHashMap[String, Unit]): String =
    val names = used.asScala.keySet
    def freshIdent: String =
      val name = Naming.freshIdent(base, names)
      if used.put(name, ()) == null then name else freshIdent
    freshIdent

  private def freshIdent(base: Symbol, used: ConcurrentHashMap[String, Unit]): Symbol =
    Symbol(freshIdent(base.name, used))

  def freshIdent(base: String)(using UniqueNaming): String =
    freshIdent(base, summon.used)

  def freshIdent(base: Symbol)(using UniqueNaming): Symbol =
    Symbol(freshIdent(base.name, summon.used))


  sealed trait PotentialNames[R <: UniqueNames[Term] | Term](using val names: UniqueNaming):
    private[UniqueNames] inline def used = names.used
    private[UniqueNames] def makeResult(expr: Term): R

  sealed trait PotentialNamesFallback:
    given[CompileToDef]: PotentialNames[UniqueNames[Term]](using UniqueNaming(ConcurrentHashMap())) with
      private[UniqueNames] def makeResult(expr: Term) = UniqueNames(expr)

  object PotentialNames extends PotentialNamesFallback:
    given(using UniqueNaming): PotentialNames[Term] with
      private[UniqueNames] def makeResult(expr: Term) = expr

  def convert[R <: UniqueNames[Term] | Term](
      expr: Term,
      used: IterableOnce[String] = Iterable.empty)(using names: PotentialNames[R]): R =
    def renamePattern(pattern: Pattern): (Pattern, Map[Symbol, Symbol]) = pattern match
      case Match(ctor, args) =>
        let(args.map(renamePattern).unzip) { (args, substs) =>
          Match(pattern)(ctor, args) -> substs.fold(Map.empty) { _ ++ _ }
        }
      case Bind(ident) =>
        val fresh = freshIdent(ident, names.used)
        Bind(pattern)(fresh) -> Map(ident -> fresh)

    def renameTerm(term: Term, subst: Map[Symbol, Symbol]): Term = term match
      case Abs(properties, ident, tpe, expr) =>
        val fresh = freshIdent(ident, names.used)
        Abs(term)(properties, fresh, tpe, renameTerm(expr, subst + (ident -> fresh)))
      case App(properties, expr, arg) =>
        App(term)(properties, renameTerm(expr, subst), renameTerm(arg, subst))
      case TypeAbs(ident, expr) =>
        TypeAbs(term)(ident, renameTerm(expr, subst))
      case TypeApp(expr, tpe) =>
        TypeApp(term)(renameTerm(expr, subst), tpe)
      case Data(ctor, args) =>
        Data(term)(ctor, args map { renameTerm(_, subst) })
      case Var(ident) =>
        subst.get(ident) map { Var(term)(_) } getOrElse term
      case Cases(scrutinee, cases) =>
        let(renameTerm(scrutinee, subst)) { scrutinee =>
          val renamedCases = cases map { (pattern, expr) =>
            let(renamePattern(pattern)) { (pattern, additionalSubst) =>
              pattern -> renameTerm(expr, subst ++ additionalSubst)
            }
          }
          Cases(term)(scrutinee, renamedCases)
        }

    let(expr.syntactic) { (expr, syntactic) =>
      syntactic.freeVars foreach { (ident, _) => names.used.put(ident.name, ()) }
      used.iterator foreach { names.used.put(_, ()) }
      names.makeResult(renameTerm(expr, Map.empty))
    }
end UniqueNames

object UniformNames:
  def convert(expr: Term): Term =
    def renamePattern(pattern: Pattern, names: Set[String]): (Pattern, Map[Symbol, Symbol], Set[String]) = pattern match
      case Match(ctor, args) =>
        val (argPatterns, argSubsts, argNames) =
          args.foldLeft(List.empty[Pattern], Map.empty[Symbol, Symbol], names) { case ((args, substs, names), arg) =>
            let(renamePattern(arg, names)) { (arg, additionalSubst, names) =>
              (arg :: args, substs ++ additionalSubst, names)
            }
          }
        (Match(pattern)(ctor, argPatterns.reverse), argSubsts, argNames)
      case Bind(ident) =>
        val fresh = Naming.freshIdent(ident, names)
        (Bind(pattern)(fresh), Map(ident -> fresh), names + fresh.name)

    def renameTerm(term: Term, names: Set[String], subst: Map[Symbol, Symbol]): (Term, Set[String]) = term match
      case Abs(properties, ident, tpe, expr) =>
        val fresh = Naming.freshIdent(ident, names)
        let(renameTerm(expr, names + fresh.name, subst + (ident -> fresh))) { Abs(term)(properties, fresh, tpe, _) -> _ }
      case App(properties, expr, arg) =>
        let(renameTerm(expr, names, subst)) { (expr, names) =>
          let(renameTerm(arg, names, subst)) { App(term)(properties, expr, _) -> _ }
        }
      case TypeAbs(ident, expr) =>
        let(renameTerm(expr, names, subst)) { TypeAbs(term)(ident, _) -> _ }
      case TypeApp(expr, tpe) =>
        let(renameTerm(expr, names, subst)) { TypeApp(term)(_, tpe) -> _ }
      case Data(ctor, args) =>
        val (argTerms, argNames) =
          args.foldLeft(List.empty[Term], names) { case ((args, names), arg) =>
            let(renameTerm(arg, names, subst)) { (arg, names) => (arg :: args) -> names }
          }
        Data(term)(ctor, argTerms.reverse) -> argNames
      case Var(ident) =>
        (subst.get(ident) map { Var(term)(_) } getOrElse term) -> names
      case Cases(scrutinee, cases) =>
        val (scrutineeTerm, scrutineeNames) = renameTerm(scrutinee, names, subst)
        val (casesPatternTerms, casesNames) =
          cases.foldLeft(List.empty[(Pattern, Term)], scrutineeNames) { case ((cases, names), pattern -> expr) =>
            let(renamePattern(pattern, names)) { (pattern, additionalSubst, names) =>
              let(renameTerm(expr, names, subst ++ additionalSubst)) { (expr, names) =>
                ((pattern -> expr) :: cases) -> names
              }
            }
          }
        Cases(term)(scrutineeTerm, casesPatternTerms.reverse) -> casesNames

    let(expr.syntactic) { (expr, syntactic) =>
      let(renameTerm(expr, (syntactic.freeVars map { (ident, _) => ident.name }).toSet, Map.empty)) { (expr, _) => expr }
    }
end UniformNames
