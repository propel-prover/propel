package ast

export Property.*
export Case.*
export Term.*

type Properties = Set[Property]

enum Property:
  case Commutative

enum Case:
  case Pattern(ident: Symbol, args: List[Case])
  case Bind(ident: Symbol)

enum Term:
  case Abs(properties: Properties, args: List[Symbol], expr: Term)
  case App(properties: Properties, expr: Term, args: List[Term])
  case Ident(ident: Symbol)
  case Let(ident: Symbol, bound: Term, expr: Term)
  case Cases(scrutinee: Term, cases: List[(Case, Term)])
