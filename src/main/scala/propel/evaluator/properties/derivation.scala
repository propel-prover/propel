package propel
package evaluator
package properties

import ast.*

def normalize(expr: Term, equalities: Equalities): Term =
  val updated = normalizing.foldLeft(expr) { (expr, normalize) => normalize(equalities).applyOrElse(expr, _ => expr) }
  if updated != expr then normalize(updated, equalities) else updated

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
