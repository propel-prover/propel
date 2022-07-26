package propel
package typer

import ast.*
import util.*

inline def join(tpe0: Type, tpe1: Type): Option[Type] =
  bound(tpe0, tpe1, 1)

inline def meet(tpe0: Type, tpe1: Type): Option[Type] =
  bound(tpe0, tpe1, -1)

inline def conforms(sub: Type, base: Type): Boolean =
  join(sub, base) exists { equivalent(_, base) }

def normalize(tpe: Type): Option[Type] =
  bound(tpe, tpe, 2)

def simplify(tpe: Type): Option[Type] =
  bound(tpe, tpe, 3)

inline def wellFormed(tpe: Type): Boolean =
  normalize(tpe).isDefined

def equivalent(tpe0: Type, tpe1: Type): Boolean =
  if tpe0 ne tpe1 then tpe0 -> tpe1 match
    case Function(arg0, result0) -> Function(arg1, result1) =>
      equivalent(arg0, arg1) && equivalent(result0, result1)
    case Universal(ident0, result0) -> Universal(ident1, result1) =>
      if ident0 == ident1 then
        equivalent(result0, result1)
      else
        equivalent(result0, subst(result1, Map(ident1 -> TypeVar(ident0))))
    case Recursive(ident0, result0) -> Recursive(ident1, result1) =>
      if ident0 == ident1 then
        equivalent(result0, result1)
      else
        equivalent(result0, subst(result1, Map(ident1 -> TypeVar(ident0))))
    case TypeVar(ident0) -> TypeVar(ident1) =>
      ident0 == ident1
    case Sum(sum0) -> Sum(sum1) =>
      Sums.equivalent(sum0, sum1)
    case (tpe0: Recursive) -> _ =>
      unfold(tpe0) exists { equivalent(_, tpe1) }
    case _ -> (tpe1: Recursive) =>
      unfold(tpe1) exists { equivalent(tpe0, _) }
    case _ =>
      false
  else
    true

private def bound(tpe0: Type, tpe1: Type, direction: Int): Option[Type] = tpe0 -> tpe1 match
  case Function(arg0, result0) -> Function(arg1, result1) =>
    bound(arg0, arg1, -direction) flatMap { arg =>
      bound(result0, result1, direction) map { result => fold(Function(tpe0)(arg, result)) }
    }
  case Universal(ident0, result0) -> Universal(ident1, result1) =>
    let(if ident0 == ident1 then result1 else subst(result1, Map(ident1 -> TypeVar(ident0)))) { result1 =>
      bound(result0, result1, direction) map { result => fold(Universal(tpe0)(ident0, result)) }
    }
  case Recursive(ident0, result0) -> Recursive(ident1, result1) =>
    let(if ident0 == ident1 then result1 else subst(result1, Map(ident1 -> TypeVar(ident0)))) { result1 =>
      bound(result0, result1, direction) map { result => fold(Recursive(tpe0)(ident0, result)) }
    }
  case TypeVar(ident0) -> TypeVar(ident1) =>
    Option.when(ident0 == ident1)(tpe0)
  case Sum(sum0) -> Sum(sum1) =>
    Sums.bound(sum0, sum1, direction) map { sum => fold(Sum(tpe0)(sum)) }
  case (tpe0: Recursive) -> _ =>
    unfold(tpe0) flatMap { bound(_, tpe1, direction) map fold }
  case _ -> (tpe1: Recursive) =>
    unfold(tpe1) flatMap { bound(tpe0, _, direction) map fold }
  case _ =>
    None

private object Sums:
  type Element = (Constructor, List[Type])
  type Sum = List[Element]
  type FlaggedSum = List[(Element, Boolean)]

  def equivalent(element0: Element, element1: Element): Boolean =
    val (ctor0, args0) = element0
    val (ctor1, args1) = element1
    ctor0 == ctor1 && (args0.size == args1.size) && (args0 zip args1 forall { typer.equivalent(_, _) })

  def equivalent(sum0: Sum, sum1: Sum): Boolean =
    def flag(sum: FlaggedSum, element: Element): (FlaggedSum, Boolean) = sum match
      case sumElement -> sumElementFlagged :: tail =>
        let(equivalent(sumElement, element), flag(tail, element)) { case (equivalent, (tail, flagged)) =>
          (sumElement -> (equivalent || sumElementFlagged) :: tail) -> (equivalent || flagged)
        }
      case _ =>
        Nil -> false

    val flaggedSum = sum0.foldLeft[Option[FlaggedSum]](Some(sum1 map { _ -> false})) {
      case (Some(flaggedSum), element) =>
        let(flag(flaggedSum, element)) { (flaggedSum, flag) => Option.when(flag)(flaggedSum) }
      case _ =>
        None
    }

    flaggedSum exists { _ forall { (_, flag) => flag } }

  def bound(sum0: Sum, sum1: Sum, direction: Int): Option[Sum] =
    def contains(sum: Sum, element: Element): Boolean =
      val (ctor, args) = element
      sum exists {
        case `ctor` -> sumElementArgs => args.size == sumElementArgs.size
        case _ => false
      }

    if sum0 eq sum1 then
      if direction == 1 || direction == -1 then
        bound(sum0, direction)
      else
        normalize(sum0, direction)
    else if direction == 1 then
      bound(sum0 ++ sum1, direction)
    else if direction == -1 then
      bound((sum0 filter { contains(sum1, _) }) ++ (sum1 filter { contains(sum0, _) }), direction)
    else
      normalize(sum0 ++ sum1, direction)

  def bound(sum: Sum, direction: Int): Option[Sum] =
    sum match
      case ctor -> args0 :: tail0 =>
        def processTail(args0: List[Type], sum: Sum): Option[(List[Type], Sum)] = sum match
          case `ctor` -> args1 :: tail1 if args0.size == args1.size =>
            args0 zip args1 mapIfDefined { typer.bound(_, _, direction) } flatMap { processTail(_, tail1) }
          case head :: tail =>
            processTail(args0, tail) map { (args, sum) => args -> (head :: sum) }
          case _ =>
            Some(args0, Nil)

        processTail(args0, tail0) match
          case Some(args, tail) => bound(tail, direction) map { (ctor -> args) :: _ }
          case _ => None

      case _ =>
        Some(Nil)

  def normalize(args: Sum, direction: Int): Option[Sum] = args match
    case (element0 @ (ctor -> args0)) :: tail0 =>
      def processTail(args: Sum): Option[Option[Sum]] = args match
        case (element1 @ (`ctor` -> args1)) :: tail1 =>
          val sum0 = List(ctor -> args0)
          val sum1 = List(ctor -> args1)
          val tpe = bound(sum0, sum1, if direction > 0 then 1 else -1)
          if tpe exists { equivalent(_, sum1) } then
            Some(None)
          else if tpe exists { equivalent(_, sum0) } then
            processTail(tail1)
          else if direction == 2 || direction == -2 then
            None
          else
            processTail(tail1) map { _ map { element1 :: _ } }
        case head :: tail =>
          processTail(tail) map { _ map { head :: _ } }
        case _ =>
          Some(Some(Nil))

      processTail(tail0) match
        case Some(Some(tail)) => normalize(tail, direction) map { element0 :: _ }
        case Some(_) => normalize(tail0, direction)
        case _ => None

    case Nil =>
      Some(Nil)
end Sums
