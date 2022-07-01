package ast

type Properties = Set[Property]

enum Property:
  case Commutative

enum Ident:
  case Term(name: String)
  case Type(name: String)

enum Case:
  case Pattern(name: Ident.Type, args: List[Case])
  case Bind(name: Ident.Term)

enum Term:
  case Abs(properties: Properties, cases: List[(List[Case], Term)])
  case App(expr: Term, args: List[Term])
  case Var(name: Ident.Term)
  case Ctor(name: Ident.Type, args: List[Term])
  case Let(properties: Properties, name: Ident.Term, bound: Term, expr: Term)
