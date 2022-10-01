package propel
package evaluator
package properties

import ast.*

def normalize(normalizing: List[Equalities => PartialFunction[Term, Term]], expr: Term, equalities: Equalities): Term =
  explode(normalizing, expr, equalities).max

def explode(normalizing: List[Equalities => PartialFunction[Term, Term]], expr: Term, equalities: Equalities): Set[Term] =
  val maxSize = expr.size * 11 / 10 + 8
  val maxBit = 8
  val max = 1 << maxBit

  val normalize = normalizing map { _(equalities) }

  def top(n: Int, exprs: Set[Term]) =
    if exprs.size <= n then exprs
    else if n <= 1 then Set(exprs.max)
    else exprs.toList.sorted.takeRight(n).toSet

  def process(term: Term): Set[Term] =
    val processed = term match
      case Abs(_, _, _, _) | TypeAbs(_, _) | Cases(_, _) | Var(_) =>
        Set(term)
      case App(properties, expr, arg) =>
        val max = 1 << (maxBit / 2)
        top(max, process(expr)) flatMap { expr =>
          top(max, process(arg)) map { arg =>
            val result = App(term)(properties, expr, arg).withSyntacticInfo
            val overlap = expr.syntacticInfo.boundVars exists { arg.syntacticInfo.boundVars contains _ }
            if overlap then UniqueNames.convert(result) unwrap { _.withSyntacticInfo } else result
          }
        }
      case TypeApp(expr, tpe) =>
        process(expr) map { TypeApp(term)(_, tpe).withSyntacticInfo }
      case Data(ctor, args) =>
        val max = if args.nonEmpty then 1 << (maxBit / args.size) else 1
        val processedArgs = args.foldRight(Set(List.empty[Term])) { (arg, args) =>
          top(max, process(arg)) flatMap { arg => args map { arg :: _ } }
        }
        processedArgs map { args =>
          val result = Data(term)(ctor, args).withSyntacticInfo
          val (_, overlap) = args.foldLeft[(Set[Symbol], Boolean)](Set.empty -> false) {
            case (result @ (_, true), _) => result
            case ((idents, _), arg) =>
              val bound = arg.syntacticInfo.boundVars
              if bound exists { idents contains _ } then Set.empty -> true else idents ++ bound -> false
          }
          if overlap then UniqueNames.convert(result) unwrap { _.withSyntacticInfo } else result
        }

    def explode(exprs: Set[Term], exploded: Set[Term]): Set[Term] =
      val (continue, stop) = (normalize.iterator
        flatMap { exprs collect _ }
        filterNot { exploded contains _ }
        map { _.withSyntacticInfo }
        partition { _.size < maxSize })

      val continueSet = continue.toSet
      val stopSet = stop.toSet

      if continueSet.nonEmpty then
        explode(continueSet, exploded ++ continueSet ++ stopSet)
      else
        exploded ++ continueSet ++ stopSet

    top(max, explode(processed, processed))

  process(expr.withSyntacticInfo)
end explode

def derive(
    derivingCompound: List[Equalities => PartialFunction[((Term, Term), (Term, Term)), List[Equalities]]],
    derivingSimple: List[Equalities => PartialFunction[(Term, Term), List[Equalities]]],
    equalities: Equalities): List[Equalities] =
  def deriveByProperties[T](
      equalities: Equalities,
      deriving: List[Equalities => PartialFunction[T, List[Equalities]]],
      exprs: T) =
    deriving.foldLeft(List(equalities)) { (equalities, derive) =>
      equalities flatMap { equalities =>
        (derive(equalities) andThen { _ flatMap equalities.withEqualities }).applyOrElse(exprs, _ => List(equalities))
      }
    }

  def process(equalities: Equalities, pos: List[(Term, Term)]): List[Equalities] = pos match
    case exprs0 :: tail0 =>
      def processTail(equalities: Equalities, pos: List[(Term, Term)]): List[Equalities] = pos match
        case exprs1 :: tail1 =>
          deriveByProperties(equalities, derivingCompound, exprs0 -> exprs1) flatMap { processTail(_, tail1) }
        case _ =>
          List(equalities)

      deriveByProperties(equalities, derivingSimple, exprs0) flatMap { processTail(_, tail0) flatMap { process(_, tail0) } } 
    case _ =>
      List(equalities)

  (process(equalities, equalities.pos.toList.sorted) flatMap { updated =>
    if updated != equalities then derive(derivingCompound, derivingSimple, updated) else List(updated)
  }).distinct
end derive
