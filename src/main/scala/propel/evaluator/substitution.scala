package propel
package evaluator

import ast.*

type TermSubstitutions = Map[Symbol, Term]

def subst(expr: Term, substs: TermSubstitutions): Term =
  substs foreach { (ident, bound) =>
    def countIdent(expr: Term, ident: Symbol): Int = expr match
      case Abs(_, arg, expr) => countIdent(expr, ident)
      case App(_, expr, arg) => countIdent(expr, ident) + countIdent(arg, ident)
      case Data(_, args) => (args map { countIdent(_, ident) }).sum
      case Let(_, bound, expr) => countIdent(bound, ident) + countIdent(expr, ident)
      case Cases(scrutinee, cases) => countIdent(scrutinee, ident) + (cases map { (_, expr) => countIdent(expr, ident) }).sum
      case Var(`ident`) => 1
      case _ => 0

    def containsLambda(expr: Term): Boolean = expr match
      case Abs(_, _, _) => true
      case App(_, expr, arg) => containsLambda(expr) || containsLambda(arg)
      case Data(_, args) => args exists containsLambda
      case Let(_, bound, expr) => containsLambda(bound) || containsLambda(expr)
      case Cases(scrutinee, cases) => containsLambda(scrutinee) || (cases exists { (_, expr) => containsLambda(expr) })
      case _ => false

    if containsLambda(bound) && countIdent(expr, ident) > 1 then
      Util.fail("Implementation restriction: "+
        s"expression bound to ${ident.name} cannot be used multiple times because it contains lambda expressions")
  }

  def bound(pattern: Pattern): List[Symbol] = pattern match
    case Match(_, args) => args flatMap bound
    case Bind(ident) => List(ident)

  def subst(term: Term, substs: TermSubstitutions): Term = term match
    case Abs(properties, arg, expr) =>
      Abs(term)(properties, arg, subst(expr, substs - arg))
    case App(properties, expr, arg) =>
      App(term)(properties, subst(expr, substs), subst(arg, substs))
    case Data(ctor, args) =>
      Data(term)(ctor, args map { subst(_, substs) })
    case Var(ident) =>
      substs.getOrElse(ident, term)
    case Let(ident, bound, expr) =>
      Let(term)(ident, subst(bound, substs), subst(expr, substs - ident))
    case Cases(scrutinee, cases) =>
      Cases(term)(
        subst(scrutinee, substs),
        cases map { (pattern, expr) =>
          pattern -> subst(expr, substs -- bound(pattern))
        })

  subst(expr, substs)

type PatternSubstitutions = Map[Symbol, Pattern]

def subst(pattern: Pattern, substs: PatternSubstitutions): Pattern = pattern match
  case Match(ctor, args) =>
    Match(pattern)(ctor, args map { subst(_, substs) })
  case Bind(ident) =>
    substs.getOrElse(ident, pattern)
