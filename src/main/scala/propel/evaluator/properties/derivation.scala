package propel
package evaluator
package properties

import ast.*
import scala.collection.mutable

def normalize(normalizing: List[Equalities => PartialFunction[Term, Term]], expr: Term, equalities: Equalities): Term =
  val maxSize = expr.size * 11 / 10 + 8
  val maxBit = 8
  val max = 1 << maxBit

  val cache = mutable.Map.empty[(Term, Term => Option[Term]), Option[Term]]

  val normalize = normalizing map { normalizing =>
    val normalize = normalizing(equalities).lift
    (expr: Term) => cache.getOrElseUpdate(expr -> normalize, normalize(expr))
  }

  def top(n: Int, exprs: Iterable[Term]) =
    if exprs.sizeIs <= n then exprs.toSet
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

    val exploded = mutable.Set.from(processed)

    def explode(exprs: Iterable[Term]): Unit =
      val (continue, stop) = (normalize.iterator
        flatMap { exprs flatMap _ }
        filterNot { exploded contains _ }
        map { _.withSyntacticInfo }
        partition { _.size < maxSize })

      if continue.nonEmpty then
        val continueIterable = continue.to(Iterable)
        exploded ++= continueIterable
        exploded ++= stop
        explode(continueIterable)
      else
        exploded ++= continue
        exploded ++= stop

    explode(processed)

    top(max, exploded)
  end process

  process(expr.withSyntacticInfo).max
end normalize

def derive(
    derivingCompound: List[Equalities => PartialFunction[((Term, Term), (Term, Term)), List[Equalities]]],
    derivingSimple: List[Equalities => PartialFunction[(Term, Term), List[Equalities]]],
    equalities: Equalities): List[Equalities] =
  val cache = collection.mutable.Map.empty[(List[Equalities => PartialFunction[Nothing, List[Equalities]]], Any, Equalities), List[Equalities]]

  def deriveByProperties[T](
      equalities: Equalities,
      deriving: List[Equalities => PartialFunction[T, List[Equalities]]],
      exprs: T) =
    cache.getOrElseUpdate(
      (deriving, exprs, equalities),
      deriving.foldLeft(List(equalities)) { (equalities, derive) =>
        equalities flatMap { equalities =>
          (derive(equalities) andThen { _ flatMap equalities.withEqualities }).applyOrElse(exprs, _ => List(equalities))
        }
      })

  def derive(
      derivingCompound: List[Equalities => PartialFunction[((Term, Term), (Term, Term)), List[Equalities]]],
      derivingSimple: List[Equalities => PartialFunction[(Term, Term), List[Equalities]]],
      equalities: Equalities): List[Equalities] =
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

  derive(derivingCompound, derivingSimple, equalities)
end derive
