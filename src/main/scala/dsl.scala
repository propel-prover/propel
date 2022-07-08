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

extension (expr: Term) def show: String =
  def show(expr: Term | Constructor): List[String] =
    val falseMatch = Match(False, List.empty)
    val falseApp = App(Set.empty, False, List.empty)
    val trueMatch = Match(True, List.empty)
    val trueApp = App(Set.empty, True, List.empty)

    val indent = "  "

    def annotation(properties: Properties) =
      if properties.isEmpty then "" else s"[${properties.show}] "

    def indented(values: List[String]) =
      if values forall { _ startsWith indent } then values else values map { indent + _ }

    def flatten(values: (String | List[String])*) = (values map {
        case value: String => List(value)
        case value: List[String] => value
      }).flatten.toList

    def parenthesize(values: List[String]) =
      if values.lengthCompare(1) > 0 then
        flatten(s"(${values.head}", values.init.tail, s"${values.last})")
      else
        flatten(s"(${values.head})")

    def ensureParenthesis(expr: Term) = expr match
      case _: (App | Var) => show(expr)
      case _ => parenthesize(show(expr))

    def binaryOp(op: String, a: Term, b: Term) =
      val aOp = ensureParenthesis(a)
      val bOp = ensureParenthesis(b)
      if aOp.lengthCompare(1) > 0 || bOp.lengthCompare(1) > 0 then
        parenthesize(aOp.head :: indented(flatten(aOp.tail, op, indented(bOp))))
      else
        parenthesize(flatten(s"${aOp.head} $op ${bOp.head}"))

    expr match
      case Cases(a, List(`trueMatch` -> `falseApp`, `falseMatch` -> `trueApp`)) =>
        val casess = ensureParenthesis(a)
        flatten(s"¬${casess.head}", casess.tail)
      case Cases(a, List(`trueMatch` -> `trueApp`, `falseMatch` -> b)) =>
        binaryOp("∨", a, b)
      case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `falseApp`)) =>
        binaryOp("∧", a, b)
      case Cases(a, List(`trueMatch` -> b, `falseMatch` -> `trueApp`)) =>
        binaryOp("→", a, b)
      case Cases(cond, List(`trueMatch` -> thenBranch, `falseMatch` -> elseBranch)) =>
        val condexpr = show(cond)
        val thenexpr = show(thenBranch)
        val elsexpr = show(elseBranch)
        if condexpr.lengthCompare(1) > 0 then
          flatten("if", indented(condexpr), "then", indented(thenexpr), "else", indented(elsexpr))
        else if thenexpr.lengthCompare(1) > 0 || elsexpr.lengthCompare(1) > 0 then
          flatten(s"if ${ensureParenthesis(cond).head} then", indented(thenexpr), "else", indented(elsexpr))
        else
          flatten(s"if ${ensureParenthesis(cond).head} then ${ensureParenthesis(thenBranch).head} else ${ensureParenthesis(elseBranch).head}")
      case Constructor(ident) =>
        flatten(ident.name)
      case Abs(properties, args, expr) =>
        val absexpr = show(expr)
        flatten(s"λ ${annotation(properties)}${args.map(_.name).mkString(" ")}. ${absexpr.head}", indented(absexpr.tail))
      case App(_, ctor: Constructor, List()) if ctor == True || ctor == False || (ctor.ident.name.headOption exists { _.isUpper }) =>
        show(ctor)
      case App(_, expr: Var, List()) if expr.ident.name.headOption exists { _.isUpper } =>
        show(expr)
      case App(_, expr, List()) =>
        parenthesize(show(expr))
      case App(properties, expr, args) =>
        val appexprs = expr :: args map {
          case expr: (Abs | Cases | Let) => parenthesize(show(expr))
          case expr =>
            val appexpr = show(expr)
            if appexpr.lengthCompare(1) > 0 then parenthesize(appexpr) else appexpr
        }
        val appexpr = appexprs.flatten
        if appexprs exists { _.lengthCompare(1) > 0 } then
          parenthesize(flatten(s"${annotation(properties)}${appexpr.head}", indented(appexpr.tail)))
        else
          parenthesize(flatten(s"${annotation(properties)}${appexpr.mkString(" ")}"))
      case Var(ident) =>
        flatten(ident.name)
      case Let(ident, bound: (Abs | Cases), expr) =>
        val letbound = show(bound)
        flatten(s"let ${ident.name} = ${letbound.head}", indented(letbound.tail), "in", indented(show(expr)))
      case Let(ident, bound, expr) =>
        val letbound = show(bound)
        val letexpr = show(expr)
        if letbound.lengthCompare(1) > 0 then
          flatten(s"let ${ident.name} =", indented(letbound), "in", indented(letexpr))
        else if letexpr.lengthCompare(1) > 0 then
          flatten(s"let ${ident.name} = ${letbound.head} in", indented(letexpr))
        else
          flatten(s"let ${ident.name} = ${letbound.head} in ${letexpr.head}")
      case Cases(scrutinee, cases) =>
        val casesscrutinee = ensureParenthesis(scrutinee)
        val caselist = cases map { (pattern, expr) =>
          val caseexpr = show(expr)
          flatten(s"${pattern.show} ⇒ ${caseexpr.head}", indented(caseexpr.tail))
        }
        if casesscrutinee.lengthCompare(1) > 0 then
          flatten("cases", indented(casesscrutinee), "of", indented(caselist.flatten))
        else
          flatten(s"cases ${casesscrutinee.head} of", indented(caselist.flatten))

  show(expr).mkString("\n")
