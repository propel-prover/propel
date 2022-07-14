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

given Ordering[Constructor] = order[Constructor].by(_.ident)

given Ordering[Pattern] =
  case (pattern0: Match, pattern1: Match) =>
    order[Match].by(_.ctor).orElseBy(_.args).compare(pattern0, pattern1)
  case (pattern0: Bind, pattern1: Bind) =>
    order[Bind].by(_.ident).compare(pattern0, pattern1)
  case (pattern0: Product, pattern1: Product) =>
    pattern0.productPrefix compare pattern1.productPrefix

given Ordering[Term] =
  case (expr0: Abs, expr1: Abs) =>
    order[Abs].by(_.arg).orElseBy(_.expr).compare(expr0, expr1)
  case (expr0: App, expr1: App) =>
    order[App].by(_.expr).orElseBy(_.arg).compare(expr0, expr1)
  case (expr0: Data, expr1: Data) =>
    order[Data].by(_.ctor).orElseBy(_.args).compare(expr0, expr1)
  case (expr0: Var, expr1: Var) =>
    order[Var].by(_.ident).compare(expr0, expr1)
  case (expr0: Let, expr1: Let) =>
    order[Let].by(_.ident).orElseBy(_.bound).orElseBy(_.expr).compare(expr0, expr1)
  case (expr0: Cases, expr1: Cases) =>
    order[Cases].by(_.scrutinee).orElseBy(_.cases).compare(expr0, expr1)
  case (expr0: Product, expr1: Product) =>
    expr0.productPrefix compare expr1.productPrefix
