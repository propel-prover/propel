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

given identType: Ordering[Ident.Type] = _.name compare _.name

given identTerm: Ordering[Ident.Term] = _.name compare _.name

given Ordering[Properties] = (properties0, properties1) =>
  if properties0.subsetOf(properties1) then -1
  else if properties1.subsetOf(properties0) then 1
  else 0

given Ordering[Case] =
  case (case0: Case.Pattern, case1: Case.Pattern) =>
    order[Case.Pattern].by(_.name).orElseBy(_.args).compare(case0, case1)
  case (case0: Case.Bind, case1: Case.Bind) =>
    order[Case.Bind].by(_.name).compare(case0, case1)
  case (case0, case1) =>
    case0.ordinal - case1.ordinal

given Ordering[Term] =
  case (expr0: Term.Abs, expr1: Term.Abs) =>
    order[Term.Abs].by(_.properties).orElseBy(_.cases).compare(expr0, expr1)
  case (expr0: Term.App, expr1: Term.App) =>
    order[Term.App].by(_.expr).orElseBy(_.args).compare(expr0, expr1)
  case (expr0: Term.Var, expr1: Term.Var) =>
    order[Term.Var].by(_.name).compare(expr0, expr1)
  case (expr0: Term.Ctor, expr1: Term.Ctor) =>
    order[Term.Ctor].by(_.name).orElseBy(_.args).compare(expr0, expr1)
  case (expr0: Term.Let, expr1: Term.Let) =>
    order[Term.Let].by(_.properties).orElseBy(_.name).orElseBy(_.bound).orElseBy(_.expr).compare(expr0, expr1)
  case (expr0, expr1) =>
    expr0.ordinal - expr1.ordinal
