package propel
package ast
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
  extension (expr: T) def make: List[(Symbol, Type, Term)]

object BindingExpr:
  given base[T: TermExpr]: BindingExpr[((String, Type), T)] =
    case ((name, tpe), expr) => List((Symbol(name), tpe, expr.make))
  given tuple1[T: TermExpr]: BindingExpr[((String, Type), T) *: EmptyTuple] =
    case ((name, tpe), expr) *: EmptyTuple => List((Symbol(name), tpe, expr.make))
  given tupleN[T: TermExpr, R <: Tuple: BindingExpr]: BindingExpr[((String, Type), T) *: R] =
    case ((name, tpe), expr) *: rest => (Symbol(name), tpe, expr.make) :: rest.make


trait TypeExpr[T]:
  extension (expr: T) def make: Type

object TypeExpr:
  given baseExpr[T <: Type]: TypeExpr[T] = expr => expr
  given stringExpr: TypeExpr[String] = expr => TypeVar(Symbol(expr))
  given pairExpr[A: TypeExpr, B: TypeExpr]: TypeExpr[(A, B)] =
    case arg -> result => Function(arg.make, result.make)


trait SumTypeExpr[T]:
  extension (expr: T) def make: List[(Constructor, List[Type])]

trait SumTypeExprBase:
  trait TypeList[T]:
    extension (expr: T) def make: List[Type]

  given typeTuple1[T: TypeExpr]: TypeList[T *: EmptyTuple] =
    case expr *: EmptyTuple => List(expr.make)
  given typeTupleN[T: TypeExpr, R <: Tuple: TypeList]: TypeList[T *: R] =
    case expr *: rest => expr.make :: rest.make

  given sumN[T <: Tuple: TypeList]: SumTypeExpr[String *: T] =
    case (name *: exprs) => List(Constructor(Symbol(name)) -> exprs.make)
  given sum0[R <: Tuple: SumTypeExpr]: SumTypeExpr[String] =
    case name => List(Constructor(Symbol(name)) -> List.empty)

object SumTypeExpr extends SumTypeExprBase:
  given tuple0sum: SumTypeExpr[EmptyTuple] =
    case EmptyTuple => List.empty
  given tupleNsumN[T <: Tuple: TypeList, R <: Tuple: SumTypeExpr]: SumTypeExpr[(String *: T) *: R] =
    case (name *: exprs) *: rest => Constructor(Symbol(name)) -> exprs.make :: rest.make
  given tupleNsum0[R <: Tuple: SumTypeExpr]: SumTypeExpr[String *: R] =
    case name *: rest => Constructor(Symbol(name)) -> List.empty :: rest.make
