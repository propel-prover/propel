package propel
package ast

import util.*

case class Syntactic(bound: Set[Symbol], free: Map[Symbol, Int], closed: Boolean, value: Boolean)

object Syntactic:
  private def merge(free: List[Map[Symbol, Int]]) =
    free.foldLeft(Map.empty[Symbol, Int]) { (free0, free1) =>
      free0 ++ (free1 map { (ident, count) => ident -> (count + free0.getOrElse(ident, 0)) })
    }


  object Pattern extends Enrichment.Intrinsic[Pattern, Syntactic]:
    val asInstance =
      case e: Syntactic => e

    def make(pattern: Pattern) = pattern match
      case Match(ctor, args) =>
        let(args.withInfo(Syntactic.Pattern)) { (args, argsInfos) =>
          val bound = argsInfos flatMap { _.bound }
          Match(pattern)(ctor, args) -> Syntactic(bound.toSet, Map.empty, closed = true, value = false)
        }
      case Bind(ident) =>
        pattern -> Syntactic(Set(ident), Map.empty, closed = true, value = false)


  object Term extends Enrichment.Intrinsic[Term, Syntactic]:
    val asInstance =
      case e: Syntactic => e

    def make(term: Term) = term match
      case Abs(properties, ident, expr) =>
        let(expr.withInfo(Syntactic.Term)) { (expr, exprInfo) =>
          val bound = exprInfo.bound + ident
          val free = exprInfo.free - ident
          Abs(term)(properties, ident, expr) -> Syntactic(bound, free, closed = free.isEmpty, value = true)
        }
      case App(properties, expr, arg) =>
        let(expr.withInfo(Syntactic.Term)) { (expr, exprInfo) =>
          let(arg.withInfo(Syntactic.Term)) { (arg, argInfo) =>
            val bound = exprInfo.bound ++ argInfo.bound
            val free = merge(List(exprInfo.free, argInfo.free))
            App(term)(properties, expr, arg) -> Syntactic(bound, free, closed = free.isEmpty, value = false)
          }
        }
      case Data(ctor, args) =>
        let(args.withInfo(Syntactic.Term)) { (args, argsInfos) =>
          val bound = argsInfos flatMap { _.bound }
          val free = merge(argsInfos map { _.free })
          Data(term)(ctor, args) -> Syntactic(bound.toSet, free, closed = free.isEmpty, value = argsInfos forall { _.value })
        }
      case Var(ident) =>
        term -> Syntactic(Set.empty, Map(ident -> 1), closed = false, value = false)
      case Cases(scrutinee, cases) =>
        let(scrutinee.withInfo(Syntactic.Term)) { (scrutinee, scrutineeInfo) =>
          val (updatedcases, bound, free) = (cases map { (pattern, expr) =>
            let(pattern.withInfo(Syntactic.Pattern)) { (pattern, patternInfo) =>
              let(expr.withInfo(Syntactic.Term)) { (expr, exprInfo) =>
                (pattern -> expr,
                 exprInfo.bound ++ patternInfo.bound,
                 exprInfo.free -- patternInfo.bound)
              }
            }
          }).unzip3

          let(merge(free)) { free =>
            Cases(term)(scrutinee, updatedcases) -> Syntactic(bound.flatten.toSet, free, closed = free.isEmpty, value = false)
          }
        }
