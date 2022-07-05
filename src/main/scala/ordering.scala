package ordering

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

given Ordering[Case] =
  case (case0: Pattern, case1: Pattern) =>
    order[Pattern].by(_.ident).orElseBy(_.args).compare(case0, case1)
  case (case0: Bind, case1: Bind) =>
    order[Bind].by(_.ident).compare(case0, case1)
  case (case0, case1) =>
    case0.ordinal - case1.ordinal

given Ordering[Term] =
  case (expr0: Abs, expr1: Abs) =>
    order[Abs].by(_.args).orElseBy(_.expr).compare(expr0, expr1)
  case (expr0: App, expr1: App) =>
    order[App].by(_.expr).orElseBy(_.args).compare(expr0, expr1)
  case (expr0: Ident, expr1: Ident) =>
    order[Ident].by(_.ident).compare(expr0, expr1)
  case (expr0: Let, expr1: Let) =>
    order[Let].by(_.ident).orElseBy(_.bound).orElseBy(_.expr).compare(expr0, expr1)
  case (expr0: Cases, expr1: Cases) =>
    order[Cases].by(_.scrutinee).orElseBy(_.cases).compare(expr0, expr1)
  case (expr0, expr1) =>
    expr0.ordinal - expr1.ordinal
