package propel
package evaluator

import ast.*
import math.Ordering.Implicits.given

def order[T] = OrderBy[T]()

final class OrderBy[T]:
  def by[S: Ordering](f: T => S): Ordering[T] = (lhs, rhs) => f(lhs) compare f(rhs)

given [T](using ord: Ordering[T]): AnyRef with
  extension (lhs: T)
    def <(rhs: T) = ord.lt(lhs, rhs)
    def <=(rhs: T) = ord.lteq(lhs, rhs)
    def >(rhs: T) = ord.gt(lhs, rhs)
    def >=(rhs: T) = ord.gteq(lhs, rhs)
    def equiv(rhs: T) = ord.equiv(lhs, rhs)
    def max(rhs: T) = ord.max(lhs, rhs)
    def min(rhs: T) = ord.min(lhs, rhs)
    def compare(rhs: T) = ord.compare(lhs, rhs)

given Ordering[Symbol] = _.name compare _.name

given Ordering[Constructor] = order[Constructor].by(_.ident)

given Ordering[Pattern] =
  case (pattern0: Match, pattern1: Match) =>
    order[Match].by(_.args).orElseBy(_.ctor).compare(pattern0, pattern1)
  case (pattern0: Bind, pattern1: Bind) =>
    order[Bind].by(_.ident).compare(pattern0, pattern1)
  case (pattern0, pattern1) =>
    def ordinal(pattern: Pattern) = pattern match
      case _: Match => 0
      case _: Bind => 1
    ordinal(pattern0) - ordinal(pattern1)

given Ordering[Type] =
  case (tpe0: Function, tpe1: Function) =>
    order[Function].by(_.arg).orElseBy(_.result).compare(tpe0, tpe1)
  case (tpe0: Universal, tpe1: Universal) =>
    order[Universal].by(_.result).orElseBy(_.ident).compare(tpe0, tpe1)
  case (tpe0: Recursive, tpe1: Recursive) =>
    order[Recursive].by(_.result).orElseBy(_.ident).compare(tpe0, tpe1)
  case (tpe0: TypeVar, tpe1: TypeVar) =>
    order[TypeVar].by(_.ident).compare(tpe0, tpe1)
  case (tpe0: Sum, tpe1: Sum) =>
    order[Sum].by(_.sum).compare(tpe0, tpe1)
  case (tpe0, tpe1) =>
    def ordinal(tpe: Type) = tpe match
      case _: Universal => 0
      case _: Recursive => 1
      case _: Function => 2
      case _: TypeVar => 3 
      case _: Sum => 4
    ordinal(tpe0) - ordinal(tpe1)

given Ordering[Term] =
  case (expr0: Abs, expr1: Abs) =>
    order[Abs].by(_.expr).orElseBy(_.tpe).orElseBy(_.ident).compare(expr0, expr1)
  case (expr0: App, expr1: App) =>
    order[App].by(_.expr).orElseBy(_.arg).compare(expr0, expr1)
  case (expr0: TypeAbs, expr1: TypeAbs) =>
    order[TypeAbs].by(_.expr).orElseBy(_.ident).compare(expr0, expr1)
  case (expr0: TypeApp, expr1: TypeApp) =>
    order[TypeApp].by(_.expr).orElseBy(_.tpe).compare(expr0, expr1)
  case (expr0: Data, expr1: Data) =>
    order[Data].by(_.args).orElseBy(_.ctor).compare(expr0, expr1)
  case (expr0: Var, expr1: Var) =>
    order[Var].by(_.ident).compare(expr0, expr1)
  case (expr0: Cases, expr1: Cases) =>
    order[Cases].by(_.scrutinee).orElseBy(_.cases).compare(expr0, expr1)
  case (expr0, expr1) =>
    def ordinal(expr: Term) = expr match
      case _: Abs => 0
      case _: TypeAbs => 1
      case _: App => 2
      case _: TypeApp => 3 
      case _: Cases => 4
      case _: Var => 5
      case _: Data => 6
    ordinal(expr0) - ordinal(expr1)
