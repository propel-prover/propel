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
