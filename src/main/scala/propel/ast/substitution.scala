package propel
package ast

import util.*

type TermSubstitutions = Map[Symbol, Term]

def subst(expr: Term, substs: TermSubstitutions): Term =
  if substs.isEmpty then
    expr
  else
    val substsTermInfos = substs.view mapValues { _.withInfo(Syntactic.Term) }
    let(expr.withInfo(Syntactic.Term), (substsTermInfos.view mapValues { (term, _) => term }).toMap) { case ((expr, exprInfo), substs) =>
      val free = (substsTermInfos.values flatMap { (_, info) => info.free.keySet }).toSet
      val used = exprInfo.bound ++ (exprInfo.free map { (ident, _) => ident }) ++ free map { _.name }

      def convert(pattern: Pattern, used: Set[String]): (Pattern, Map[Symbol, Var], Set[Symbol], Set[String]) = pattern match
        case Match(ctor, args) =>
          val converted = args.foldLeft(List.empty[Pattern], Map.empty[Symbol, Var], Set.empty[Symbol], used) {
            case ((args, substs, bindings, used), arg) =>
              let(convert(arg, used)) { (arg, argSubsts, argBindings, argUsed) =>
                (arg :: args, substs ++ argSubsts, bindings ++ argBindings, used ++ argUsed)
              }
          }
          let(converted) { (args, substs, bindings, used) => (Match(pattern)(ctor, args.reverse), substs, bindings, used) }
        case Bind(ident) if free contains ident =>
          val fresh = Util.freshIdent(ident, used)
          (Bind(pattern)(fresh), Map(ident -> Var(fresh)), Set.empty, used + fresh.name)
        case Bind(ident) =>
          (pattern, Map.empty, Set(ident), used)

      def subst(term: Term, used: Set[String], substs: TermSubstitutions): Term = term match
        case Abs(properties, ident, expr) if free contains ident =>
          val fresh = Util.freshIdent(ident, used)
          Abs(term)(properties, fresh, subst(expr, used + fresh.name, substs + (ident -> Var(fresh))))
        case Abs(properties, ident, expr) =>
          Abs(term)(properties, ident, subst(expr, used, substs - ident))
        case App(properties, expr, arg) =>
          App(term)(properties, subst(expr, used, substs), subst(arg, used, substs))
        case Data(ctor, args) =>
          Data(term)(ctor, args map { subst(_, used, substs) })
        case Var(ident) =>
          substs.get(ident) match
            case Some(Var(ident)) => Var(term)(ident)
            case Some(expr) => expr
            case _ => term
        case Cases(scrutinee, cases) =>
          Cases(term)(
            subst(scrutinee, used, substs),
            cases map { (pattern, expr) =>
              let(convert(pattern, used)) { (pattern, patternSubsts, patternBindings, used) =>
                pattern -> subst(expr, used, substs ++ patternSubsts -- patternBindings)
              }
            })

      subst(expr, used, substs)
    }
end subst

type PatternSubstitutions = Map[Symbol, Pattern]

def subst(pattern: Pattern, substs: PatternSubstitutions): Pattern =
  def subst(pattern: Pattern, substs: PatternSubstitutions): (Pattern, PatternSubstitutions) = pattern match
    case Match(ctor, args) =>
      val substituted = args.reverseIterator.foldLeft(List.empty[Pattern], substs) { case ((args, substs), arg) =>
        if substs.nonEmpty then
          let(subst(arg, substs)) { (arg, substs) => (arg :: args) -> substs }
        else
          (arg :: args) -> substs
      }
      let(substituted) { (args, substs) => Match(pattern)(ctor, args) -> substs }
    case Bind(ident) =>
      substs.get(ident) match
        case Some(pattern) => pattern -> (substs - ident)
        case _ => pattern -> substs

  if substs.nonEmpty then
    let(subst(pattern, substs)) { (pattern, _) => pattern }
  else
    pattern
end subst
