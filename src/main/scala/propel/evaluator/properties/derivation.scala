package propel
package evaluator
package properties

import ast.*

def normalize(normalizing: List[Equalities => PartialFunction[Term, Term]], expr: Term, equalities: Equalities): Term =
  explode(normalizing, expr, equalities).max

def explode(normalizing: List[Equalities => PartialFunction[Term, Term]], expr: Term, equalities: Equalities): Set[Term] =
  val normalize = normalizing map { _(equalities) }

  def process(term: Term): Set[Term] =
    val processed = term match
      case Abs(_, _, _, _) | TypeAbs(_, _) | Cases(_, _) | Var(_) =>
        Set(term)
      case App(properties, expr, arg) =>
        process(expr) flatMap { expr => process(arg) map { App(term)(properties, expr, _) } }
      case TypeApp(expr, tpe) =>
        process(expr) map { TypeApp(term)(_, tpe) }
      case Data(ctor, args) =>
        val processedArgs = args.foldRight(Set(List.empty[Term])) { (arg, args) =>
          process(arg) flatMap { arg => args map { arg :: _ } }
        }
        processedArgs map { Data(term)(ctor, _) }

    def explode(exprs: Set[Term], exploded: Set[Term]): Set[Term] =
      val updated = (normalize flatMap { exprs collect _ }).toSet -- exploded
      if updated.nonEmpty then explode(updated, exploded ++ updated) else exploded

    explode(processed, processed)

  process(expr)
end explode

def derive(equalities: Equalities): Option[Equalities] =
  def deriveByProperties[T](
      equalities: Equalities,
      deriving: List[Equalities => PartialFunction[T, (Term, Term)]],
      exprs: T) =
    deriving.foldLeft[Option[Equalities]](Some(equalities)) {
      case (Some(equalities), derive) =>
        (derive(equalities) andThen equalities.withEqualities).applyOrElse(exprs, _ => Some(equalities))
      case _ =>
        None
    }

  def process(equalities: Equalities, pos: List[(Term, Term)]): Option[Equalities] = pos match
    case exprs0 :: tail0 =>
      def processTail(equalities: Equalities, pos: List[(Term, Term)]): Option[Equalities] = pos match
        case exprs1 :: tail1 =>
          deriveByProperties(equalities, derivingCompound, exprs0 -> exprs1) flatMap { processTail(_, tail1) }
        case _ =>
          Some(equalities)

      deriveByProperties(equalities, derivingSimple, exprs0) flatMap {
        processTail(_, tail0) flatMap { process(_, tail0) }
      } 
    case _ =>
      Some(equalities)

  process(equalities, equalities.pos.toList) flatMap { updated =>
    if updated != equalities then derive(updated) else Some(updated)
  }
end derive
