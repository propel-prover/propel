package propel
package dsl

import ast.*


export ast.Term
export ast.Constructor.{False, True}


type TermExpr[T] = dsl.impl.TermExpr.Base[T]

type PatternExpr[T] = dsl.impl.PatternExpr.Base[T]

type CaseExpr[T] = dsl.impl.CaseExpr[T]

type BindingExpr[T] = dsl.impl.BindingExpr[T]


def comm = Commutative

def assoc = Associative

def idem = Idempotent

def refl = Reflexive

def irefl = Irreflexive

def sym = Symmetric

def antisym = Antisymmetric

def asym = Asymmetric

def conn = Connected

def trans = Transitive


def term[A: TermExpr](expr: A): Term =
  expr.make

def abs[A: TermExpr](ident: String, idents: String*)(expr: A): Term =
  abs()(ident, idents*)(expr)

def abs[A: TermExpr](properties: Property*)(ident: String, idents: String*)(expr: A): Term =
  Abs(properties.toSet, Symbol(ident), idents.foldRight(expr.make) { (ident, expr) => Abs(Set.empty, Symbol(ident), expr) })

def app[A <: (Tuple | Term | String): TermExpr](expr: A): Term =
  app()(expr)

def app[A <: (Tuple | Term | String): TermExpr](properties: Property*)(expr: A): Term =
  def decorate(expr: Term): Term = expr match
    case App(properties, expr: App, arg) => App(properties, decorate(expr), arg)
    case App(_, expr, arg) => App(properties.toSet, expr, arg)
    case _ => expr
  decorate(expr.make)

def let[A: PatternExpr, B: TermExpr, C: TermExpr](binding: (A, B))(expr: C): Term =
  val (pattern, bound) = binding
  val boundExpr = bound.make

  val (_, info) = boundExpr.withInfo(Syntactic.Term)
  val free = (info.free map { (ident, _) => ident.name }).toSet
  val valName = Util.freshIdent("val", free)

  app()(abs()(valName)(cases(valName)(pattern -> expr)), boundExpr)

def letrec[A: BindingExpr, B: TermExpr](binding: A)(expr: B): Term =
  val fix = abs("f")(abs("x")("f", abs("v")(("x", "x"), "v")), abs("x")("f", abs("v")(("x", "x"), "v")))

  val (idents, exprs) = binding.make.unzip
  val free = (exprs flatMap { expr =>
    val (_, info) = expr.withInfo(Syntactic.Term)
    info.free map { (ident, _) => ident.name }
  }).toSet

  val recName = Util.freshIdent("rec", free)
  val wildcardName = Util.freshIdent("_", free)

  val pattern = Match(Constructor(Symbol("Tuple")), idents map { Bind(_) })
  val substs = (idents map { ident => ident -> let(pattern -> app()(recName, "Unit"))(Var(ident)) }).toMap
  val rec = abs(recName, wildcardName)(subst(Data(Constructor(Symbol("Tuple")), exprs), substs))
  let(pattern -> app()(fix, rec))(expr.make)

def cases[A: TermExpr, B: CaseExpr](scrutinee: A)(cases: B): Term =
  Cases(scrutinee.make, cases.make)

def pattern[A: PatternExpr](expr: A): Pattern =
  expr.make match
    case expr: Match => expr
    case expr: Bind => Match(Constructor(expr.ident), List.empty)


package sugar:
  def not[A: TermExpr](a: A) = cases(a)(True -> False, False -> True)

  def or[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> True, False -> b)

  def and[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> b, False -> False)

  def implies[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> b, False -> True)

  def `if`[A: TermExpr, B: TermExpr, C: TermExpr](a: A)(b: B)(c: C) = cases(a)(True -> b, False -> c)
