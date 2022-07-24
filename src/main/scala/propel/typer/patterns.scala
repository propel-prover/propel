package propel
package typer

import ast.*
import util.*

def diff(tpe: Type, pattern: Pattern): Option[Type] = tpe -> pattern match
  case _ -> Bind(_) =>
    Some(tpe)
  case (tpe: Recursive) -> _ =>
    unfold(tpe) flatMap { diff(_, pattern) } map fold
  case Sum(sum) -> Match(ctor, matchArgs) =>
    val elements = sum flatMap {
      case `ctor` -> sumArgs if sumArgs.size == matchArgs.size =>
        let(sumArgs zip matchArgs map diff) { args =>
          if args exists { _.isEmpty } then
            Some(None)
          else if (args collectFirst { case Some(Sum(List())) => }).isDefined ||
                  (args zip sumArgs forall { _.get eq _ }) then
            None
          else
            Some(Some(ctor -> args.flatten))
        }
      case element =>
        Some(Some(element))
    }
    elements.sequenceIfDefined map { Sum(_) }
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
