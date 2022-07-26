package propel
package typer

import ast.*
import util.*

def diff(tpe: Type, pattern: Pattern): Option[Type] = tpe -> pattern match
  case _ -> Bind(_) =>
    Some(Sum(List()))
  case (tpe: Recursive) -> _ =>
    unfold(tpe) flatMap { diff(_, pattern) } map fold
  case Sum(sum) -> Match(ctor, matchArgs) =>
    val elements = sum map {
      case `ctor` -> sumArgs if sumArgs.size == matchArgs.size =>
        def process(sumArgs: List[Type], matchArgs: List[Pattern]): Option[List[List[Type]]] = (sumArgs, matchArgs) match
          case (List(sumArg), List(matchArg)) =>
            diff(sumArg, matchArg) map { arg => List(List(arg)) }
          case (sumArg :: sumArgs, matchArg :: matchArgs) =>
            diff(sumArg, matchArg) flatMap { arg =>
              process(sumArgs, matchArgs) map { tails =>
                (arg :: sumArgs) :: (tails map { sumArg :: _ })
              }
            }
          case _ =>
            Some(List.empty)

        process(sumArgs, matchArgs) map {
          _ flatMap { args =>
            if (args collectFirst { case Sum(List()) => }).isDefined then
              None
            else
              Some(ctor -> args)
          }
        }

      case element =>
        Some(List(element))
    }
    elements.sequenceIfDefined flatMap { sum => simplify(Sum(sum.flatten)) }
  case _ =>
    None

def patterns(tpe: Type): List[Pattern] = tpe match
  case Sum(sum) =>
    sum flatMap { (ctor, args) =>
      val argsPatterns = (args map patterns).foldRight(List(List.empty[Pattern])) { (argPatterns, argsPatterns) =>
        argPatterns flatMap { argPattern => argsPatterns map { argPattern :: _ } }
      }
      argsPatterns map { Match(ctor, _) }
    }
  case _ =>
    List(Bind(Symbol("□")))
