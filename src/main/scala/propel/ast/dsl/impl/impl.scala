package propel
package dsl
package impl

import ast.*

trait Expr[T, U](lower: Symbol => T, upper: Symbol => U, compound: U => T):
  trait Base[V]:
    extension (expr: V)
      def make = expr.makeImpl(false)
      private[impl] def makeNested = expr.makeImpl(true)
      private[impl] def makeImpl: Boolean => T

  trait Rest[V <: Tuple]:
    extension (expr: V)
      def make: List[T]

  given baseExpr[T0 <: T]: Base[T0] = expr => _ => expr
  given compoundExpr[U0 <: U]: Base[U0] = expr => _ => compound(expr)
  given stringExpr: Base[String] = expr => _ =>
    if expr.headOption exists { _.isUpper } then compound(upper(Symbol(expr)))
    else lower(Symbol(expr))

  given baseTuple1[V: Base]: Rest[V *: EmptyTuple] =
    case expr *: _ => List(expr.make)
  given baseTupleN[V: Base, R <: Tuple: Rest]: Rest[V *: R] =
    case expr *: rest => expr.make :: rest.make


object TermExpr extends Expr(Var(_), Constructor(_), Data(_, List.empty)):
  given baseTuple[T: TermExpr, R <: Tuple: Rest]: Base[T *: R] =
    case expr *: rest => _ => expr.makeNested match
      case Data(expr, List()) => Data(expr, rest.make)
      case expr => rest.make.foldLeft(expr) { App(Set.empty, _, _) }


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


trait BindingExpr[T]:
  extension (expr: T) def make: List[(Symbol, Term)]

trait BindingExprBase:
  given base1[T: TermExpr]: BindingExpr[(String, T)] =
    case (name, expr) => List(Symbol(name) -> expr.make)

object BindingExpr extends BindingExprBase:
  given tuple1[T: TermExpr]: BindingExpr[(String, T) *: EmptyTuple] =
    case (name, expr) *: EmptyTuple => List(Symbol(name) -> expr.make)
  given tupleN[T: TermExpr, R <: Tuple: BindingExpr]: BindingExpr[(String, T) *: R] =
    case (name, expr) *: rest => (Symbol(name) -> expr.make) :: rest.make
