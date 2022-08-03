package propel
package ast

import util.*
import scala.annotation.targetName

type TermSubstitutions = Map[Symbol, Term]

@targetName("substTermsInTerm")
def subst(expr: Term, substs: TermSubstitutions): Term =
  if substs.isEmpty then
    expr
  else
    val substsTermInfos = substs.view mapValues { _.withIntrinsicInfo(Syntactic.Term) }
    let(expr.withIntrinsicInfo(Syntactic.Term), (substsTermInfos.view mapValues { (term, _) => term }).toMap) { case ((expr, exprInfo), substs) =>
      val free = (substsTermInfos.values flatMap { (_, info) => info.freeVars.keySet }).toSet
      val used = exprInfo.boundVars ++ (exprInfo.freeVars map { (ident, _) => ident }) ++ free map { _.name }

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
          val fresh = Naming.freshIdent(ident, used)
          (Bind(pattern)(fresh), Map(ident -> Var(fresh)), Set.empty, used + fresh.name)
        case Bind(ident) =>
          (pattern, Map.empty, Set(ident), used)

      def subst(term: Term, used: Set[String], substs: TermSubstitutions): Term = term match
        case Abs(properties, ident, tpe, expr) if free contains ident =>
          val fresh = Naming.freshIdent(ident, used)
          Abs(term)(properties, fresh, tpe, subst(expr, used + fresh.name, substs + (ident -> Var(fresh))))
        case Abs(properties, ident, tpe, expr) =>
          Abs(term)(properties, ident, tpe, subst(expr, used, substs - ident))
        case App(properties, expr, arg) =>
          App(term)(properties, subst(expr, used, substs), subst(arg, used, substs))
        case TypeAbs(ident, expr) =>
          TypeAbs(term)(ident, subst(expr, used, substs))
        case TypeApp(expr, tpe) =>
          TypeApp(term)(subst(expr, used, substs), tpe)
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

@targetName("substPatternsInPattern")
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

type TypeSubstitutions = Map[Symbol, Type]

@targetName("substTypesInType")
def subst(tpe: Type, substs: TypeSubstitutions): Type =
  if substs.isEmpty then
    tpe
  else
    val substsTypeInfos = substs.view mapValues { _.withIntrinsicInfo(Syntactic.Type) }
    let(tpe.withIntrinsicInfo(Syntactic.Type), (substsTypeInfos.view mapValues { (tpe, _) => tpe }).toMap) { case ((tpe, tpeInfo), substs) =>
      val free = (substsTypeInfos.values flatMap { (_, info) => info.freeTypeVars }).toSet
      val used = tpeInfo.boundTypeVars ++ tpeInfo.freeTypeVars ++ free map { _.name }

      def subst(tpe: Type, used: Set[String], substs: TypeSubstitutions): Type = tpe match
        case Function(arg, result) =>
          Function(tpe)(subst(arg, used, substs), subst(result, used, substs))
        case Universal(ident, result) if free contains ident =>
          val fresh = Naming.freshIdent(ident, used)
          Universal(tpe)(fresh, subst(result, used + fresh.name, substs + (ident -> TypeVar(fresh))))
        case Universal(ident, result) =>
          Universal(tpe)(ident, subst(result, used, substs - ident))
        case Recursive(ident, result) if free contains ident =>
          val fresh = Naming.freshIdent(ident, used)
          Recursive(tpe)(fresh, subst(result, used + fresh.name, substs + (ident -> TypeVar(fresh))))
        case Recursive(ident, result) =>
          Recursive(tpe)(ident, subst(result, used, substs - ident))
        case TypeVar(ident) =>
          substs.get(ident) match
            case Some(TypeVar(ident)) => TypeVar(tpe)(ident)
            case Some(tpe) => tpe
            case _ => tpe
        case Sum(sum) =>
          Sum(sum map { (ctor, args) => ctor -> (args map { subst(_, used, substs) }) })

      subst(tpe, used, substs)
    }
end subst

@targetName("substTypesInTerm")
def subst(expr: Term, substs: TypeSubstitutions): Term =
  if substs.isEmpty then
    expr
  else
    val substsTypeInfos = substs.view mapValues { _.withIntrinsicInfo(Syntactic.Type) }
    let(expr.withIntrinsicInfo(Syntactic.Term), (substsTypeInfos.view mapValues { (tpe, _) => tpe }).toMap) { case ((tpe, tpeInfo), substs) =>
      val free = (substsTypeInfos.values flatMap { (_, info) => info.freeTypeVars }).toSet
      val used = tpeInfo.boundTypeVars ++ tpeInfo.freeTypeVars ++ free map { _.name }

      def subst(term: Term, used: Set[String], substs: TypeSubstitutions): Term = term match
        case Abs(properties, ident, tpe, expr) =>
          Abs(term)(properties, ident, ast.subst(tpe, substs), subst(expr, used, substs))
        case TypeAbs(ident, expr) if free contains ident =>
          val fresh = Naming.freshIdent(ident, used)
          TypeAbs(term)(fresh, subst(expr, used + fresh.name, substs + (ident -> TypeVar(fresh))))
        case TypeAbs(ident, expr) =>
          TypeAbs(term)(ident, subst(expr, used, substs - ident))
        case TypeApp(expr, tpe) =>
          TypeApp(term)(subst(expr, used, substs), ast.subst(tpe, substs))
        case App(properties, expr, arg) =>
          App(term)(properties, subst(expr, used, substs), subst(arg, used, substs))
        case Data(ctor, args) =>
          Data(term)(ctor, args map { subst(_, used, substs) })
        case Var(ident) =>
          term
        case Cases(scrutinee, cases) =>
          Cases(term)(subst(scrutinee, used, substs), cases map { (pattern, expr) => pattern -> subst(expr, used, substs) })

      subst(expr, used, substs)
    }
end subst
