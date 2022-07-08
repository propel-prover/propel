package dsl

import ast.*


export ast.Term
export ast.Constructor.{False, True}


package impl:
  trait Expr[T, U](lower: Symbol => T, upper: Symbol => U, compound: U => T):
    trait Base[V]:
      extension (expr: V)
        def make = expr.makeImpl(false)
        private[impl] def makeNested = expr.makeImpl(true)
        private[impl] def makeImpl: Boolean => T

    trait Rest[V <: Tuple]:
      extension (expr: V)
        def make = expr.makeImpl(false)
        private[impl] def makeNested = expr.makeImpl(true)
        private[impl] def makeImpl: Boolean => List[T]

    given baseExpr: Base[T] = expr => _ => expr
    given compoundExpr: Base[U] = expr => _ => compound(expr)
    given stringExpr: Base[String] = expr => _ =>
      if expr.headOption exists { _.isUpper } then compound(upper(Symbol(expr)))
      else lower(Symbol(expr))

    given baseTuple1[V: Base]: Rest[V *: EmptyTuple] =
      case expr *: _ => EmptyTuple => List(expr.make)
    given baseTupleN[V: Base, R <: Tuple: Rest]: Rest[V *: R] =
      case expr *: rest => _ => expr.make :: rest.make


  object TermExpr extends Expr(Var(_), Constructor(_), App(Set.empty, _, List.empty)):
    given baseTuple[T: TermExpr, R <: Tuple: Rest]: Base[T *: R] =
      case expr *: rest => _ => expr.makeNested match
        case App(_, expr, _) => App(Set.empty, expr, rest.make)
        case expr => App(Set.empty, expr, rest.make)


  object PatternExpr extends Expr(Bind(_), Constructor(_), Match(_, List.empty)):
    given stringTuple[R <: Tuple: Rest]: Base[String *: R] =
      case expr *: rest => _ => Match(Constructor(Symbol(expr)), rest.make)


  trait CaseExpr[T]:
    extension (expr: T) def make: List[(Pattern, Term)]

  trait CaseExprBase:
    given base1[P: PatternExpr, T: TermExpr]: CaseExpr[(P, T)] =
      case (pattern, expr) => List(pattern.make -> expr.make)

  object CaseExpr extends CaseExprBase:
    given tuple1[P: PatternExpr, T: TermExpr]: CaseExpr[(P, T) *: EmptyTuple] =
      case (pattern, expr) *: EmptyTuple => List(pattern.make -> expr.make)
    given tupleN[P: PatternExpr, T: TermExpr, R <: Tuple: CaseExpr]: CaseExpr[(P, T) *: R] =
      case (pattern, expr) *: rest => (pattern.make -> expr.make) :: rest.make


type TermExpr[T] = impl.TermExpr.Base[T]

type PatternExpr[T] = impl.PatternExpr.Base[T]

type CaseExpr[T] = impl.CaseExpr[T]


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

def abs[A: TermExpr](args: String*)(expr: A): Term =
  Abs(Set.empty, args.map(Symbol(_)).toList, expr.make)

def abs[A: TermExpr](properties: Property*)(args: String*)(expr: A): Term =
  Abs(properties.toSet, args.map(Symbol(_)).toList, expr.make)

def app[A <: (Tuple | Term | String): TermExpr](expr: A): Term =
  expr.make match
    case expr: App => expr
    case expr => App(Set.empty, expr, List.empty)

def app[A <: (Tuple | Term | String): TermExpr](properties: Property*)(expr: A): Term =
  expr.make match
    case expr: App => expr.copy(properties = properties.toSet)
    case expr => App(properties.toSet, expr, List.empty)

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



extension (property: Property) def show: String = property match
  case Commutative => "comm"
  case Associative => "assoc"
  case Idempotent => "idem"
  case Reflexive => "refl"
  case Irreflexive => "irefl"
  case Symmetric => "sym"
  case Antisymmetric => "antisym"
  case Asymmetric => "asym"
  case Connected => "conn"
  case Transitive => "trans"

extension (properties: Properties) def show: String =
  properties.map(_.show).mkString(", ")

extension (pattern: Pattern) def show: String = pattern match
  case Match(ctor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) => ctor.ident.name
  case Match(ctor, List()) => s"(${ctor.ident.name})"
  case Match(ctor, args) => s"(${ctor.ident.name} ${args.map(_.show).mkString(" ")})"
  case Bind(ident) => ident.name

extension (patterns: List[Pattern]) def show: String =
  s"❬${patterns.map(_.show).mkString(", ")}❭"

extension (expr: Term) def show: String =
  def show(expr: Term | Constructor, indent: Int): String =
    def showDirect(expr: Term | Constructor) = show(expr, indent)
    def showInline(expr: Term | Constructor) = show(expr, indent + 1)
    def showAlinged(output: String) = s"\n${"  " * indent}$output"
    def showIndented(output: String) = s"\n${"  " * (indent + 1)}$output"
    def annotation(properties: Properties) = if properties.isEmpty then "" else s"[${properties.show}] "

    expr match
      case Constructor(ident) =>
        ident.name
      case Abs(properties, args, expr) =>
        s"λ ${annotation(properties)}${args.map(_.name).mkString(" ")}. ${showInline(expr)}"
      case App(_, ctor: Constructor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
        showDirect(ctor)
      case App(_, expr: Var, List()) if expr.ident.name.headOption exists { _.isUpper } =>
        showDirect(expr)
      case App(_, expr, List()) =>
        s"(${showInline(expr)})"
      case App(properties, expr, args) =>
        s"(${annotation(properties)}${showInline(expr)} ${(args map {
          case arg: (Let | Cases) => s"(${showInline(arg)})"
          case arg => showInline(arg)
        }).mkString(" ")})"
      case Var(ident) =>
        ident.name
      case Let(ident, bound, expr) =>
        s"let ${ident.name} = ${showInline(bound)}${showAlinged("in")}${showIndented(showInline(expr))}"
      case Cases(scrutinee: (App | Var), cases) =>
        s"cases ${showInline(scrutinee)} of${cases.map((cases, expr) => showIndented(s"${cases.show} ⇒ ${showInline(expr)}")).mkString}"
      case Cases(scrutinee, cases) =>
        s"cases (${showInline(scrutinee)}) of${cases.map((cases, expr) => showIndented(s"${cases.show} ⇒ ${showInline(expr)}")).mkString}"

  show(expr, 0)
