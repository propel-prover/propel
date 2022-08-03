package propel
package ast

import ast.*
import util.*

def equivalent(tpe0: Type, tpe1: Type): Boolean =
  typer.normalize(tpe0) exists { tpe0 => typer.normalize(tpe1) exists { typer.equal(tpe0, _) } }

def equivalent(expr0: Term, expr1: Term): Boolean =
  def substs(pattern0: Pattern, pattern1: Pattern): Option[Map[Symbol, Var]] = pattern0 -> pattern1 match
    case Match(_, args0) -> Match(_, args1) => args0 zip args1 mapIfDefined substs map { _.flatten.toMap }
    case Bind(ident0) -> Bind(ident1) => if ident0 == ident1 then Some(Map.empty) else Some(Map(ident1 -> Var(ident0)))
    case _ => None

  expr0 -> expr1 match
    case Abs(properties0, ident0, tpe0, expr0) -> Abs(properties1, ident1, tpe1, expr1) =>
      if ident0 == ident1 then
        properties0 == properties1 && equivalent(tpe0, tpe1) && equivalent(expr0, expr1)
      else
        properties0 == properties1 && equivalent(tpe0, tpe1) && equivalent(expr0, subst(expr1, Map(ident1 -> Var(ident0))))
    case App(properties0, expr0, arg0) -> App(properties1, expr1, arg1) =>
      properties0 == properties1 && equivalent(expr0, expr1) && equivalent(arg0, arg1)
    case TypeAbs(ident0, expr0) -> TypeAbs(ident1, expr1) =>
      if ident0 == ident1 then
        equivalent(expr0, expr1)
      else
        equivalent(expr0, subst(expr1, Map(ident1 -> TypeVar(ident0))))
    case TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) =>
      equivalent(expr0, expr1) && equivalent(tpe0, tpe1)
    case Data(ctor0, args0) -> Data(ctor1, args1) =>
      ctor0 == ctor1 && (args0 zip args1 forall { equivalent(_, _) })
    case Var(ident0) -> Var(ident1) =>
      ident0 == ident1
    case Cases(scrutinee0, cases0) -> Cases(scrutinee1, cases1) =>
      equivalent(scrutinee0, scrutinee1) && (cases0 zip cases1 forall {
        case (pattern0 -> expr0) -> (pattern1 -> expr1) =>
          substs(pattern0, pattern1) match
            case Some(substs) => if substs.isEmpty then equivalent(expr0, expr1) else equivalent(expr0, subst(expr1, substs))
            case _ => false
      })
    case _ =>
      false
end equivalent
