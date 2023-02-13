package propel
package evaluator
package properties

import ast.*
import typer.*
import scala.collection.mutable

def select(
    selecting: List[Equalities => PartialFunction[Term, List[(Term, Equalities)]]],
    expr: Term,
    equalities: Equalities) =
  val selections = selecting flatMap { _(equalities).applyOrElse(expr, _ => List.empty) }
  if selections.isEmpty then
    expr match
      case App(_, Abs(_, _, _, _), _) =>
        selections
      case App(_, _, _) =>
        expr.termType match
          case Some(Sum(sum)) if sum forall { (_, args) => args.isEmpty } =>
            sum flatMap { (ctor, _) =>
              Equalities.pos(List(expr -> Data(ctor, List.empty))) map { Data(ctor, List.empty) -> _ }
            }
          case _ =>
            selections
      case _ =>
        selections
  else
    selections

def normalize(
    normalizing: List[Equalities => PartialFunction[Term, Term]],
    priorityVariable: Var => Boolean,
    contractAbstraction: Abstraction => Boolean,
    expr: Term,
    equalities: Equalities): Term =
  given Ordering[Term] = termOrderingWithPriorityVariable(priorityVariable)

  val cache = mutable.Map.empty[(Term, Term => Option[Term]), Option[Term]]

  val normalize = normalizing map { normalizing =>
    val normalize = normalizing(equalities).lift
    (expr: Term) => cache.getOrElseUpdate(expr -> normalize, normalize(expr))
  }

  def top(n: Int, exprs: Iterable[Term]) =
    if exprs.sizeIs <= n then exprs.toSet
    else if n <= 1 then Set(exprs.max)
    else exprs.toList.sorted.takeRight(n).toSet

  val abstractions =
    def merge(abstractions0: Map[Abstraction, Term], abstractions1: Map[Abstraction, Term]) =
      abstractions0.foldLeft(abstractions1) { case (result, entry0 @ (abstraction0, expr0)) =>
        (result.get(abstraction0)
          collect { case expr1 if expr1 < expr0 => result }
          getOrElse result + entry0)
      }

    def abstractions(term: Term): Map[Abstraction, Term] = term match
      case Abs(_, _, _, expr) => abstractions(expr)
      case App(_, expr, arg) => merge(abstractions(expr), abstractions(arg))
      case TypeAbs(_, expr) => abstractions(expr)
      case TypeApp(expr, _) => abstractions(expr)
      case Data(_, args) =>
        args.foldLeft[Map[Abstraction, Term]](Map.empty) { (result, arg) =>
          merge(abstractions(arg), result)
        }
      case Var(ident) =>
        (term.termType flatMap { _.info(Abstraction) } collect {
          case abstraction if contractAbstraction(abstraction) && !(equalities.pos contains term) =>
            abstraction -> term
        }).toMap
      case Cases(scrutinee, cases) =>
        cases.foldLeft(abstractions(scrutinee)) { case (result, (_, expr)) =>
          merge(abstractions(expr), result)
        }

    merge(
      abstractions(expr),
      equalities.pos flatMap { (expr0, expr1) =>
        merge(abstractions(expr0.withSyntacticInfo), abstractions(expr1.withSyntacticInfo))
      })
  end abstractions

  def normalizeAbstraction(term: Term): Term =
    term.info(Abstraction) flatMap abstractions.get getOrElse {
      term match
        case Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe, normalizeAbstraction(expr))
        case App(properties, expr, arg) => App(term)(properties, normalizeAbstraction(expr), normalizeAbstraction(arg))
        case TypeAbs(ident, expr) => TypeAbs(term)(ident, normalizeAbstraction(expr))
        case TypeApp(expr, tpe) => TypeApp(term)(normalizeAbstraction(expr), tpe)
        case Data(ctor, args) => Data(term)(ctor, args map normalizeAbstraction)
        case Var(_) => term
        case Cases(scrutinee, cases) => Cases(term)(normalizeAbstraction(scrutinee), cases map { (pattern, expr) =>
          pattern -> normalizeAbstraction(expr)
        })
    }

  def process(term: Term): Set[Term] =
    val maxSize = term.size * 11 / 10 + 8
    val maxBit = 8
    val max = 1 << maxBit

    val processed = normalizeAbstraction(term) match
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
        map normalizeAbstraction
        filterNot { exploded contains _ }
        map { _.withSyntacticInfo }
        partition { _.size < maxSize })

      if continue.nonEmpty then
        val continueIterable = continue.to(Iterable)
        exploded ++= continueIterable
        exploded ++= stop
        if exploded.size < max then
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
