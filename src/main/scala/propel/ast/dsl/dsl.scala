package propel
package dsl

import ast.*


export ast.Term
export ast.Constructor.{False, True}


type TermExpr[T] = dsl.impl.TermExpr.Base[T]

type PatternExpr[T] = dsl.impl.PatternExpr.Base[T]

type CaseExpr[T] = dsl.impl.CaseExpr[T]

type BindingExpr[T] = dsl.impl.BindingExpr[T]

type TypeExpr[T] = dsl.impl.TypeExpr[T]

type SumTypeExpr[T] = dsl.impl.SumTypeExpr[T]


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


def tm[A: TermExpr](expr: A): Term =
  expr.make

def abs[A: TermExpr](ident: (String, Type), idents: (String, Type)*)(expr: A): Term =
  abs()(ident, idents*)(expr)

def abs[A: TermExpr](properties: Property*)(typedIdent: (String, Type), typedIdents: (String, Type)*)(expr: A): Term =
  val (ident, tpe) = typedIdent
  Abs(properties.toSet, Symbol(ident), tpe, typedIdents.foldRight(expr.make) { case ((ident, tpe), expr) => Abs(Set.empty, Symbol(ident), tpe, expr) })

def app[A <: (Tuple | Term | String): TermExpr](expr: A): Term =
  app()(expr)

def tpabs[A: TermExpr](ident: String, idents: String*)(expr: A): Term =
  (ident +: idents).foldRight(expr.make) { (ident, expr) => TypeAbs(Symbol(ident), expr) }

def app[A <: (Tuple | Term | String): TermExpr](properties: Property*)(expr: A): Term =
  expr.make match
    case term @ App(_, App(_, expr, arg), _) => App(term.properties, App(properties.toSet, expr, arg), term.arg)
    case term => term

def tpapp[A <: (Tuple | Term | String): TermExpr](expr: A)(tpe: Type, tpes: Type*): Term =
  (tpe +: tpes).foldLeft(expr.make) { (expr, tpe) => TypeApp(expr, tpe) }

def let[A: PatternExpr, B: TermExpr, C: TermExpr](binding: (A, B))(expr: C): Term =
  val (pattern, bound) = binding
  cases(bound.make)(pattern.make -> expr.make)

def letrec[A: BindingExpr, B: TermExpr](binding: A)(expr: B): Term =
  val fix = tpabs("T", "U")(abs("f" -> tp(("T" -> "U") -> ("T" -> "U")))(
    abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v")),
    abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v"))))

  val (idents, tpes, exprs) = binding.make.unzip3
  val free = (exprs flatMap { expr =>
    val (_, info) = expr.withIntrinsicInfo(Syntactic.Term)
    info.freeVars map { (ident, _) => ident.name }
  }).toSet

  val recName = Naming.freshIdent("rec", free)
  val wildcardName = Naming.freshIdent("_", free)

  val tuple = Constructor(Symbol("Tuple"))
  val pattern = Match(tuple, idents map { Bind(_) })
  val tpe = Sum(List(tuple -> tpes))
  val substs = (idents map { ident => ident -> let(pattern -> app()(recName, "Unit"))(Var(ident)) }).toMap
  val fun = abs(recName -> tp(dt("Unit") -> tpe), wildcardName -> dt("Unit"))(subst(Data(tuple, exprs), substs))
  let(pattern -> app()(tpapp(fix)(dt("Unit"), tpe), fun, "Unit"))(expr.make)

def cases[A: TermExpr, B: CaseExpr](scrutinee: A)(cases: B): Term =
  Cases(scrutinee.make, cases.make)

def pattern[A: PatternExpr](expr: A): Pattern =
  expr.make match
    case expr: Match => expr
    case expr: Bind => Match(Constructor(expr.ident), List.empty)

def tp[A: TypeExpr](expr: A): Type =
  expr.make

def forall[A: TypeExpr](ident: String, idents: String*)(expr: A): Type =
  (ident +: idents).foldRight(expr.make) { (ident, tpe) => Universal(Symbol(ident), tpe) }

def rec[A: TypeExpr](ident: String)(expr: A): Type =
  Recursive(Symbol(ident), expr.make)

def dt[A: SumTypeExpr](expr: A): Type =
  Sum(expr.make)


package sugar:
  def bool = Sum(List(True -> List(), False -> List()))

  def nat = rec("X")(dt(("S", "X"), "Z"))

  def list[T: TypeExpr](t: T) = subst(rec("X")(dt(("Cons", "T", "X"), "Nil")), Map(Symbol("T") -> t.make))

  def not[A: TermExpr](a: A) = cases(a)(True -> False, False -> True)

  def or[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> True, False -> b)

  def and[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> b, False -> False)

  def implies[A: TermExpr, B: TermExpr](a: A)(b: B) = cases(a)(True -> b, False -> True)

  def `if`[A: TermExpr, B: TermExpr, C: TermExpr](a: A)(b: B)(c: C) = cases(a)(True -> b, False -> c)
