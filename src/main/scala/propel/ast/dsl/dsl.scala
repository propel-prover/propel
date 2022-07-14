package propel
package dsl

import ast.*


export ast.Term
export ast.Constructor.{False, True}


type TermExpr[T] = dsl.impl.TermExpr.Base[T]

type PatternExpr[T] = dsl.impl.PatternExpr.Base[T]

type CaseExpr[T] = dsl.impl.CaseExpr[T]


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

def abs[A: TermExpr](arg: String, args: String*)(expr: A): Term =
  abs()(arg, args*)(expr)

def abs[A: TermExpr](properties: Property*)(arg: String, args: String*)(expr: A): Term =
  Abs(properties.toSet, Symbol(arg), args.foldRight(expr.make) { (arg, expr) => Abs(Set.empty, Symbol(arg), expr) })

def app[A <: (Tuple | Term | String): TermExpr](expr: A): Term =
  app()(expr)

def app[A <: (Tuple | Term | String): TermExpr](properties: Property*)(expr: A): Term =
  def decorate(expr: Term): Term = expr match
    case App(properties, expr: App, arg) => App(properties, decorate(expr), arg)
    case App(_, expr, arg) => App(properties.toSet, expr, arg)
    case _ => expr
  decorate(expr.make)

def let[A: TermExpr, B: TermExpr](name: String, bound: A, expr: B): Term =
  Let(Symbol(name), bound.make, expr.make)

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
