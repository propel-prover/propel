package dsl

import ast.*


export ast.Term


trait Expr[T](atom: Symbol => T, compound: Symbol => T):
  trait Base[U]:
    extension (expr: U) def make: T

  trait Rest[U <: Tuple]:
    extension (expr: U) def make: List[T]

  def fromString(expr: String) =
    if expr.isEmpty || expr.head.isUpper then compound(Symbol(expr))
    else atom(Symbol(expr))

  given baseExpr: Base[T] = expr => expr
  given stringExpr: Base[String] = expr => fromString(expr)

  given baseTuple1[U: Base]: Rest[U *: EmptyTuple] =
    case expr *: EmptyTuple => List(expr.make)
  given baseTupleN[U: Base, R <: Tuple: Rest]: Rest[U *: R] =
    case expr *: rest => expr.make :: rest.make


type TermExpr[T] = TermExpr.Base[T]

object TermExpr extends Expr(Ident(_), symbol => App(Set.empty, Ident(symbol), List.empty)):
  given baseTuple[U: TermExpr, R <: Tuple: Rest]: Base[U *: R] =
    case expr *: rest => App(Set.empty, expr.make, rest.make)
  given stringTuple[R <: Tuple: Rest]: Base[String *: R] =
    case expr *: rest => App(Set.empty, Ident(Symbol(expr)), rest.make)


type PatternExpr[T] = PatternExpr.Base[T]

object PatternExpr extends Expr(Bind(_), Pattern(_, List.empty)):
  given stringTuple[R <: Tuple: Rest]: Base[String *: R] =
    case expr *: rest => Pattern(Symbol(expr), rest.make)


trait CaseExpr[T]:
  extension (expr: T) def make: List[(Case, Term)]

trait CaseExprBase:
  given base1[P: PatternExpr, T: TermExpr]: CaseExpr[(P, T)] =
    case (pattern, expr) => List(pattern.make -> expr.make)

object CaseExpr extends CaseExprBase:
  given tuple1[P: PatternExpr, T: TermExpr]: CaseExpr[(P, T) *: EmptyTuple] =
    case (pattern, expr) *: EmptyTuple => List(pattern.make -> expr.make)
  given tupleN[P: PatternExpr, T: TermExpr, R <: Tuple: CaseExpr]: CaseExpr[(P, T) *: R] =
    case (pattern, expr) *: rest => (pattern.make -> expr.make) :: rest.make


def comm = Commutative

def term[A: TermExpr](expr: A): Term =
  expr.make

def abs[A: TermExpr](arg: String, args: String*)(expr: A): Term =
  Abs(Set.empty, Symbol(arg) :: args.map(Symbol(_)).toList, expr.make)

def abs[A: TermExpr](properties: Property*)(arg: String, args: String*)(expr: A): Term =
  Abs(properties.toSet, Symbol(arg) :: args.map(Symbol(_)).toList, expr.make)

def app[A <: (Tuple | Term | String): TermExpr](expr: A): Term =
  expr.make match
    case expr: App => expr
    case expr => App(Set.empty, expr, List.empty)

def app[A <: (Tuple | Term | String): TermExpr](using DummyImplicit)(properties: Property*)(expr: A): Term =
  expr.make match
    case expr: App => expr.copy(properties = properties.toSet)
    case expr => App(properties.toSet, expr, List.empty)

def let[A: TermExpr, B: TermExpr](name: String, bound: A, expr: B): Term =
  Let(Symbol(name), bound.make, expr.make)

def cases[A: TermExpr, B: CaseExpr](scrutinee: A)(cases: B): Term =
  Cases(scrutinee.make, cases.make)

def pattern[A: PatternExpr](expr: A): Case =
  expr.make match
    case expr: Pattern => expr
    case expr: Bind => Pattern(expr.ident, List.empty)


extension (property: Property) def show: String = property match
  case Commutative => "comm"

extension (properties: Properties) def show: String =
  properties.map(_.show).mkString(", ")

extension (expr: Case) def show: String = expr match
  case Pattern(ident, List()) if ident.name.nonEmpty && ident.name.head.isUpper => ident.name
  case Pattern(ident, List()) => s"(${ident.name})"
  case Pattern(ident, args) => s"(${ident.name} ${args.map(_.show).mkString(" ")})"
  case Bind(ident) => ident.name

extension (cases: List[Case]) def show: String =
  s"❬${cases.map(_.show).mkString(", ")}❭"

extension (expr: Term) def show: String =
  def show(expr: Term, indent: Int): String =
    def showDirect(expr: Term) = show(expr, indent)
    def showInline(expr: Term) = show(expr, indent + 1)
    def showAlinged(output: String) = s"\n${"  " * indent}$output"
    def showIndented(output: String) = s"\n${"  " * (indent + 1)}$output"
    def annotation(properties: Properties) = if properties.isEmpty then "" else s"[${properties.show}] "

    expr match
      case Abs(properties, args, expr) =>
        s"λ ${annotation(properties)}${args.map(_.name).mkString(" ")}. ${showInline(expr)}"
      case App(_, expr: Ident, List()) if expr.ident.name.headOption exists { _.isUpper } =>
        showDirect(expr)
      case App(_, expr, List()) =>
        s"(${showInline(expr)})"
      case App(properties, expr, args) =>
        s"(${annotation(properties)}${showInline(expr)} ${args.map(showInline).mkString(" ")})"
      case Ident(ident) =>
        ident.name
      case Let(ident, bound, expr) =>
        s"let ${ident.name} = ${showInline(bound)}${showAlinged("in")}${showIndented(showInline(expr))}"
      case Cases(scrutinee: App, cases) =>
        s"cases ${showInline(scrutinee)} of${cases.map((cases, expr) => showIndented(s"${cases.show} ⇒ ${showInline(expr)}")).mkString}"
      case Cases(scrutinee, cases) =>
        s"cases (${showInline(scrutinee)}) of${cases.map((cases, expr) => showIndented(s"${cases.show} ⇒ ${showInline(expr)}")).mkString}"

  show(expr, 0)
