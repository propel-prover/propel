package propel
package ast

import util.*

extension (expr: Type)
  inline def syntactic: (Type, Syntactic) = expr.withIntrinsicInfo(Syntactic.Type)

extension (expr: Pattern)
  inline def syntactic: (Pattern, Syntactic) = expr.withIntrinsicInfo(Syntactic.Pattern)

extension (expr: Term)
  inline def syntactic: (Term, Syntactic) = expr.withIntrinsicInfo(Syntactic.Term)

case class Syntactic(
  boundVars: Set[Symbol], freeVars: Map[Symbol, Int],
  boundTypeVars: Set[Symbol], freeTypeVars: Set[Symbol],
  closed: Boolean, value: Boolean) extends Enrichment(Syntactic)

object Syntactic extends Enrichment.Intrinsic[Type | Pattern | Term, Syntactic]:
  extension (free: List[Map[Symbol, Int]]) private def merge =
    free.foldLeft(Map.empty[Symbol, Int]) { (free0, free1) =>
      free0 ++ (free1 map { (ident, count) => ident -> (count + free0.getOrElse(ident, 0)) })
    }

  extension [A, B, C, D, E](list: List[(A, B, C, D, E)]) private def unzip5 =
    list.foldRight(List.empty[A], List.empty[B], List.empty[C], List.empty[D], List.empty[E]) {
      case ((elementA, elementB, elementC, elementD, elementE), (listA, listB, listC, listD, listE)) =>
       (elementA :: listA, elementB :: listB, elementC :: listC, elementD :: listD, elementE :: listE)
    }

  def make(construct: Type | Pattern | Term) = construct match
    case construct: Type => Type.make(construct)
    case construct: Pattern => Pattern.make(construct)
    case construct: Term => Term.make(construct)

  object Type extends Enrichment.Intrinsic[Type, Syntactic]:
    def make(tpe: Type) = tpe match
      case Function(arg, result) =>
        let(arg.syntactic) { (arg, argInfo) =>
          let(result.syntactic) { (result, resultInfo) =>
            val boundTypeVars = argInfo.boundTypeVars ++ resultInfo.boundTypeVars
            val freeTypeVars = argInfo.freeTypeVars ++ resultInfo.freeTypeVars
            Function(tpe)(arg, result) -> Syntactic(
              Set.empty, Map.empty, boundTypeVars, freeTypeVars,
              closed = freeTypeVars.isEmpty, value = false)
          }
        }
      case Universal(ident, result) =>
        let(result.syntactic) { (result, resultInfo) =>
          val boundTypeVars = resultInfo.boundTypeVars + ident
          val freeTypeVars = resultInfo.freeTypeVars - ident
          Universal(tpe)(ident, result) -> Syntactic(
            Set.empty, Map.empty, boundTypeVars, freeTypeVars,
            closed = freeTypeVars.isEmpty, value = false)
        }
      case Recursive(ident, result) =>
        let(result.syntactic) { (result, resultInfo) =>
          val boundTypeVars = resultInfo.boundTypeVars + ident
          val freeTypeVars = resultInfo.freeTypeVars - ident
          Recursive(tpe)(ident, result) -> Syntactic(
            Set.empty, Map.empty, boundTypeVars, freeTypeVars,
            closed = freeTypeVars.isEmpty, value = false)
        }
      case TypeVar(ident) =>
        tpe -> Syntactic(
          Set.empty, Map.empty, Set.empty, Set(ident),
          closed = false, value = false)
      case Sum(sum) =>
        val (updatedsum, boundTypeVars, freeTypeVars) = (sum map { (ctor, args) =>
          let((args map { _.syntactic }).unzip) { (args, argsInfos) =>
            (ctor -> args,
             argsInfos flatMap { _.boundTypeVars },
             argsInfos flatMap { _.freeTypeVars })
          }
        }).unzip3

        Sum(tpe)(updatedsum) -> Syntactic(
          Set.empty, Map.empty, boundTypeVars.flatten.toSet, freeTypeVars.flatten.toSet,
          closed = freeTypeVars.isEmpty, value = false)
  end Type

  object Pattern extends Enrichment.Intrinsic[Pattern, Syntactic]:
    def make(pattern: Pattern) = pattern match
      case Match(ctor, args) =>
        let((args map { _.syntactic }).unzip) { (args, argsInfos) =>
          val boundVars = argsInfos flatMap { _.boundVars }
          Match(pattern)(ctor, args) -> Syntactic(
            boundVars.toSet, Map.empty, Set.empty, Set.empty, closed = true, value = false)
        }
      case Bind(ident) =>
        pattern -> Syntactic(
          Set(ident), Map.empty, Set.empty, Set.empty, closed = true, value = false)
  end Pattern

  object Term extends Enrichment.Intrinsic[Term, Syntactic]:
    def make(term: Term) = term match
      case Abs(properties, ident, tpe, expr) =>
        let(tpe.syntactic) { (tpe, tpeInfo) =>
          let(expr.syntactic) { (expr, exprInfo) =>
            val boundVars = exprInfo.boundVars ++ tpeInfo.boundVars + ident
            val freeVars = exprInfo.freeVars ++ tpeInfo.freeVars - ident
            val boundTypeVars = exprInfo.boundTypeVars ++ tpeInfo.boundTypeVars + ident
            val freeTypeVars = exprInfo.freeTypeVars ++ tpeInfo.freeTypeVars - ident
            Abs(term)(properties, ident, tpe, expr) -> Syntactic(
              boundVars, freeVars, boundTypeVars, freeTypeVars,
              closed = freeVars.isEmpty && freeTypeVars.isEmpty, value = true)
          }
        }
      case App(properties, expr, arg) =>
        let(expr.syntactic) { (expr, exprInfo) =>
          let(arg.syntactic) { (arg, argInfo) =>
            val boundVars = exprInfo.boundVars ++ argInfo.boundVars
            val freeVars = List(exprInfo.freeVars, argInfo.freeVars).merge
            val boundTypeVars = exprInfo.boundTypeVars ++ argInfo.boundTypeVars
            val freeTypeVars = exprInfo.freeTypeVars ++ argInfo.freeTypeVars
            App(term)(properties, expr, arg) -> Syntactic(
              boundVars, freeVars, boundTypeVars, freeTypeVars,
              closed = freeVars.isEmpty && freeTypeVars.isEmpty, value = false)
          }
        }
      case TypeAbs(ident, expr) =>
        let(expr.syntactic) { (expr, exprInfo) =>
          val boundTypeVars = exprInfo.boundTypeVars + ident
          val freeTypeVars = exprInfo.freeTypeVars - ident
          TypeAbs(term)(ident, expr) -> Syntactic(
            exprInfo.boundVars, exprInfo.freeVars, boundTypeVars, freeTypeVars,
            closed = exprInfo.freeVars.isEmpty && freeTypeVars.isEmpty, value = false)
        }
      case TypeApp(expr, tpe) =>
        let(expr.syntactic) { (expr, exprInfo) =>
          let(tpe.syntactic) { (tpe, tpeInfo) =>
            val boundVars = exprInfo.boundVars ++ tpeInfo.boundVars
            val freeVars = exprInfo.freeVars ++ tpeInfo.freeVars
            val boundTypeVars = exprInfo.boundTypeVars ++ tpeInfo.boundTypeVars
            val freeTypeVars = exprInfo.freeTypeVars ++ tpeInfo.freeTypeVars
            TypeApp(term)(expr, tpe) -> Syntactic(
              boundVars, freeVars, boundTypeVars, freeTypeVars,
              closed = freeVars.isEmpty && freeTypeVars.isEmpty, value = false)
          }
        }
      case Data(ctor, args) =>
        let((args map { _.syntactic }).unzip) { (args, argsInfos) =>
          val boundVars = argsInfos flatMap { _.boundVars }
          val freeVars = (argsInfos map { _.freeVars }).merge
          val boundTypeVars = argsInfos flatMap { _.boundTypeVars }
          val freeTypeVars = argsInfos flatMap { _.freeTypeVars }
          Data(term)(ctor, args) -> Syntactic(
            boundVars.toSet, freeVars, boundTypeVars.toSet, freeTypeVars.toSet,
            closed = freeVars.isEmpty && freeTypeVars.isEmpty, value = argsInfos forall { _.value })
        }
      case Var(ident) =>
        term -> Syntactic(
          Set.empty, Map(ident -> 1), Set.empty, Set.empty,
          closed = false, value = false)
      case Cases(scrutinee, cases) =>
        let(scrutinee.syntactic) { (scrutinee, scrutineeInfo) =>
          val (updatedcases, boundVars, freeVars, boundTypeVars, freeTypeVars) = (cases map { (pattern, expr) =>
            let(pattern.syntactic) { (pattern, patternInfo) =>
              let(expr.syntactic) { (expr, exprInfo) =>
                (pattern -> expr,
                 exprInfo.boundVars ++ patternInfo.boundVars,
                 exprInfo.freeVars -- patternInfo.boundVars,
                 exprInfo.boundTypeVars,
                 exprInfo.freeTypeVars)
              }
            }
          }).unzip5

          let(freeVars.merge, freeTypeVars.flatten.toSet) { (freeVars, freeTypeVars) =>
            Cases(term)(scrutinee, updatedcases) -> Syntactic(
              boundVars.flatten.toSet, freeVars, boundTypeVars.flatten.toSet, freeTypeVars,
              closed = freeVars.isEmpty && freeTypeVars.isEmpty, value = false)
          }
        }
  end Term
end Syntactic
