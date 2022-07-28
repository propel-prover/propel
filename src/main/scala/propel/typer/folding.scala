package propel
package typer

import ast.*
import util.*

def fold(tpe: Type): Type = tpe match
  case Function(arg: Recursive, result) =>
    unfold(arg) collect { case other if equal(other, tpe) => fold(arg) } getOrElse tpe
  case Function(arg, result: Recursive) =>
    unfold(result) collect { case other if equal(other, tpe) => fold(result) } getOrElse tpe
  case Universal(ident, result: Recursive) =>
    unfold(result) collect { case other if equal(other, tpe) => fold(result) } getOrElse tpe
  case Recursive(ident, result: Recursive) =>
    unfold(result) collect { case other if equal(other, tpe) => fold(result) } getOrElse tpe
  case Sum(sum) =>
    sum collectFirstDefined { case _ -> args =>
      args collectFirstDefined {
        case arg: Recursive => unfold(arg) collect { case other if equal(other, tpe) => fold(arg) }
        case _ => None
      }
    } getOrElse tpe
  case _ =>
    tpe

def unfold(tpe: Recursive): Option[Type] =
  def infinite(tpe: Type, idents: Set[Symbol]): Boolean = tpe match
    case Recursive(ident, result) => infinite(result, idents + ident)
    case TypeVar(ident) => idents contains ident
    case _ => false

  def unfold(tpe: Type): Type = tpe match
    case Recursive(ident, result) => unfold(subst(result, Map(ident -> tpe)))
    case _ => tpe

  Option.when(!infinite(tpe.result, Set(tpe.ident)))(unfold(tpe))
