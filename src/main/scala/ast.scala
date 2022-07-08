package ast

export Property.*
export Pattern.*
export Term.*

type Properties = Set[Property]

enum Property:
  case Commutative
  case Associative
  case Idempotent
  case Reflexive
  case Irreflexive
  case Symmetric
  case Antisymmetric
  case Asymmetric
  case Connected
  case Transitive

case class Constructor(ident: Symbol)

object Constructor:
  val False = Constructor(Symbol("⊥"))
  val True = Constructor(Symbol("⊤"))

enum Pattern:
  case Match(ctor: Constructor, args: List[Pattern])
  case Bind(ident: Symbol)

enum Term:
  case Abs(properties: Properties, args: List[Symbol], expr: Term)
  case App(properties: Properties, expr: Term | Constructor, args: List[Term])
  case Var(ident: Symbol)
  case Let(ident: Symbol, bound: Term, expr: Term)
  case Cases(scrutinee: Term, cases: List[(Pattern, Term)])
