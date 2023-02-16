package propel
package dsl.impl

import ast.*
import evaluator.properties.Normalization

import scala.quoted.{Type => _, *}

given SymbolToExpr: ToExpr[Symbol] with
  def apply(symbol: Symbol)(using Quotes) =
    '{ Symbol(${Expr(symbol.name)}) }

given PropertyToExpr: ToExpr[Property] with
  def apply(property: Property)(using Quotes) = property match
    case Commutative => '{ Commutative }
    case Associative => '{ Associative }
    case Idempotent => '{ Idempotent }
    case Selection => '{ Selection }
    case Reflexive => '{ Reflexive }
    case Irreflexive => '{ Irreflexive }
    case Symmetric => '{ Symmetric }
    case Antisymmetric => '{ Antisymmetric }
    case Asymmetric => '{ Asymmetric }
    case Connected => '{ Connected }
    case Transitive => '{ Transitive }

given ConstructorToExpr: ToExpr[Constructor] with
  def apply(ctor: Constructor)(using Quotes) =
    '{ Constructor(${Expr(ctor.ident)}) }

given PatternToExpr: ToExpr[Pattern] with
  def apply(pattern: Pattern)(using Quotes) = pattern match
    case Match(ctor, args) => '{ Match(${Expr(ctor)}, ${Expr(args)}) }
    case Bind(ident) => '{ Bind(${Expr(ident)}) }

given TypeToExpr: ToExpr[Type] with
  def apply(tpe: Type)(using Quotes) = tpe match
    case Function(arg, result) => '{ Function(${Expr(arg)}, ${Expr(result)}) }
    case Universal(ident, result) => '{ Universal(${Expr(ident)}, ${Expr(result)}) }
    case Recursive(ident, result) => '{ Recursive(${Expr(ident)}, ${Expr(result)}) }
    case TypeVar(ident) => '{ TypeVar(${Expr(ident)}) }
    case Sum(sum) => '{ Sum(${Expr(sum)}) }

given TermToExpr: ToExpr[Term] with
  def apply(term: Term)(using Quotes) = term match
    case Abs(properties, ident, tpe, expr) => '{ Abs(${Expr(properties)}, ${Expr(ident)}, ${Expr(tpe)}, ${Expr(expr)}) }
    case App(properties, expr, arg) => '{ App(${Expr(properties)}, ${Expr(expr)}, ${Expr(arg)}) }
    case TypeAbs(ident, expr) => '{ TypeAbs(${Expr(ident)}, ${Expr(expr)}) }
    case TypeApp(expr, tpe) => '{ TypeApp(${Expr(expr)}, ${Expr(tpe)}) }
    case Data(ctor, args) => '{ Data(${Expr(ctor)}, ${Expr(args)}) }
    case Var(ident) => '{ Var(${Expr(ident)}) }
    case Cases(scrutinee, cases) => '{ Cases(${Expr(scrutinee)}, ${Expr(cases)}) }

given NormalizationToExpr: ToExpr[Normalization] with
  def apply(normalization: Normalization)(using Quotes) =
    val Normalization(pattern, result, abstraction, variables, reversible) = normalization
    '{ Normalization(${Expr(pattern)}, ${Expr(result)}, ${Expr(abstraction)}, ${Expr(variables)}, ${Expr(reversible)}) }
