package propel
package typer

import ast.*
import util.*

class Abstraction extends Enrichment(Abstraction)

object Abstraction extends Enrichment.Extrinsic[Type | Term, Abstraction]:
  def assign(from: Option[Type], to: Type): Type =
    from map { Abstraction.assign(_, to) } getOrElse Abstraction.assign(to)

  def assign(from: Type, to: Type): Type =
    def copy(from: Type, to: Type) = from.info(Abstraction) map { to.withExtrinsicInfo(_) } getOrElse to

    def assign(from: Type, to: Type): Type = from -> to match
      case Function(fromArg, fromResult) -> Function(toArg, toResult) =>
        copy(from, Function(to)(assign(fromArg, toArg), assign(fromResult, toResult)))
      case Universal(fromIdent, fromResult) -> Universal(toIdent, toResult) =>
        if fromIdent == toIdent then
          copy(from, Universal(to)(toIdent, assign(fromResult, toResult)))
        else
          copy(from, Universal(to)(toIdent, assign(subst(fromResult, Map(fromIdent -> TypeVar(toIdent))), toResult)))
      case Recursive(fromIdent, fromResult) -> Recursive(toIdent, toResult) =>
        if fromIdent == toIdent then
          Recursive(to)(toIdent, assign(fromResult, toResult))
        else
          Recursive(to)(toIdent, assign(subst(fromResult, Map(fromIdent -> TypeVar(toIdent))), toResult))
      case Sum(fromSum) -> Sum(toSum) =>
        Sum(to)(toSum map { case sum @ (ctor -> toArgs) =>
          (fromSum
            collectFirst { case `ctor` -> fromArgs if fromArgs.size == toArgs.size =>
              ctor -> (fromArgs zip toArgs map assign)
            }
            getOrElse sum)
        })
      case _ =>
        to

    assign(from, Abstraction.assign(to))

  def assign(tpe: Type): Type =
    def assign(tpe: Type, abstractions: List[Type]): (Type, Boolean, List[Type]) = tpe match
      case Function(arg, result) =>
        let(assign(arg, abstractions)) { (arg, argAbstract, abstractions) =>
          let(assign(result, abstractions)) { (result, resultAbstract, abstractions) =>
            val tpeAbstract = argAbstract && resultAbstract
            abstractions find { _ == tpe } match
              case Some(other) =>
                (Abstraction.assign(other, Function(tpe)(arg, result)), tpeAbstract, abstractions)
              case _ =>
                val abstraction = tpe.info(Abstraction) getOrElse Abstraction()
                let(Function(tpe)(arg, result).withExtrinsicInfo(abstraction)) { tpe =>
                  (tpe, tpeAbstract, tpe :: abstractions)
                }
          }
        }
      case Universal(ident, result) =>
        let(assign(result, abstractions)) { (result, _, abstractions) =>
          (Universal(tpe)(ident, result).withExtrinsicInfo(Abstraction()), false, abstractions)
        }
      case Recursive(_, _) =>
        (tpe, false, abstractions)
      case TypeVar(_) =>
        (tpe, true, abstractions)
      case Sum(sum) =>
        val (updatedSum, updatedAbstractions) = sum.foldRight(List.empty[(Constructor, List[Type])], abstractions) {
          case ((ctor, args), (sum, abstractions)) =>
            val (updatedArgs, updatedAbstractions) = args.foldRight(List.empty[Type], abstractions) {
              case (arg, (args, abstractions)) =>
                let(assign(arg, abstractions)) { (arg, _, abstractions) => (arg :: args, abstractions) }
            }
            ((ctor -> updatedArgs) :: sum, updatedAbstractions)
        }
        (Sum(tpe)(updatedSum), false, updatedAbstractions)

    let(assign(tpe, List.empty)) { (tpe, _, _) => tpe }
end Abstraction
