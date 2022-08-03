package propel
package evaluator

import ast.*

enum Equality:
  case Equal
  case Indeterminate
  case Unequal

object Equality:
  inline def min(inline equality0: Equality, inline equality1: Equality) =
    def equality = equality1
    (equality0: equality0.type @unchecked) match
      case Unequal => Unequal
      case Equal => equality
      case Indeterminate => if equality == Unequal then Unequal else Indeterminate

  inline def max(inline equality0: Equality, inline equality1: Equality) =
    def equality = equality1
    (equality0: equality0.type @unchecked) match
      case Equal => Equal
      case Unequal => equality
      case Indeterminate => if equality == Equal then Equal else Indeterminate

  inline def neg(inline equality: Equality) =
    (equality: equality.type @unchecked) match
      case Equal => Unequal
      case Unequal => Equal
      case Indeterminate => Indeterminate
end Equality

case class Equalities private (pos: Map[Term, Term], neg: Set[Map[Term, Term]]):
  def equal(expr0: Term, expr1: Term): Equality =
    def equal(expr0: Term, expr1: Term): (Equality, List[(Term, Term)]) =
      pos.getOrElse(expr0, expr0) -> pos.getOrElse(expr1, expr1) match
        case (expr0: (Abs | TypeAbs)) -> (expr1: (Abs | TypeAbs)) if equivalent(expr0, expr1) =>
          Equality.Equal -> List.empty
        case terms @ App(_, expr0, arg0) -> App(_, expr1, arg1) =>
          equal(expr0, expr1) match
            case Equality.Unequal -> _ => Equality.Unequal -> List.empty
            case equality0 -> exprs0 =>
              val equality1 -> exprs1 = equal(arg0, arg1)
              Equality.min(equality0, equality1) -> (terms :: exprs0 ++ exprs1)
        case terms @ TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) if equivalent(tpe0, tpe1) =>
          val equality -> exprs = equal(expr0, expr1)
          equality -> (terms :: exprs)
        case terms @ Data(ctor0, args0) -> Data(ctor1, args1) =>
          if ctor0 == ctor1 && args0.size == args1.size then
            if args0.isEmpty then
              Equality.Equal -> List(terms)
            else
              val (equality, exprs) = equal(args0.head, args1.head)
              (args0.tail zip args1.tail).foldLeft(equality -> (terms :: exprs)) {
                case (Equality.Unequal -> _, _) =>
                  Equality.Unequal -> List.empty
                case (equality0 -> exprs0, arg0 -> arg1) =>
                  val equality1 -> exprs1 = equal(arg0, arg1)
                  Equality.min(equality0, equality1) -> (exprs0 ++ exprs1)
              }
          else
            Equality.Unequal -> List.empty
        case terms @ Var(ident0) -> Var(ident1) if ident0 == ident1 =>
          Equality.Equal -> List(terms)
        case terms =>
          Equality.Indeterminate -> List(terms)

    equal(expr0, expr1) match
      case (Equality.Unequal, _) =>
        Equality.Unequal
      case (equality, exprs) =>
        val unequal = neg exists {
          _ forall { (ne0, ne1) =>
            exprs exists { (expr0, expr1) =>
              equal(ne0, expr0) match
                case (Equality.Equal, _) =>
                  val equality -> _ = equal(ne1, expr1)
                  equality == Equality.Equal
                case _ =>
                  false
            }
          }
        }
        if unequal then Equality.Unequal else equality
  end equal

  def withEqualities(equalities: Equalities): Option[Equalities] =
    withEqualities(equalities.pos) flatMap { _.withUnequalities(equalities.neg) }

  def withEqualities(pos: PatternConstraints): Option[Equalities] =
    withEqualities(pos.iterator map { _ -> _.asTerm })

  def withEqualities(pos: (Term, Term)): Option[Equalities] =
    withEqualities(Iterator(pos))

  def withEqualities(pos: IterableOnce[(Term, Term)]): Option[Equalities] =
    val iterator = pos.iterator
    if iterator.nonEmpty then
      Equalities(normalize(this.pos, iterator) filterNot { _ == _ }, this.neg)
        .propagatePos.propagateNeg.consolidateNeg
    else
      Some(this)

  def withUnequalities(neg: PatternConstraints): Option[Equalities] =
    withUnequalities(List(neg.iterator map { _ -> _.asTerm }))

  def withUnequalities(neg: IterableOnce[IterableOnce[(Term, Term)]]): Option[Equalities] =
    val iterator = neg.iterator
    if iterator.nonEmpty then
      Equalities(this.pos, (iterator map { neg => normalize(Map.empty, neg.iterator) }).toSet)
        .propagateNeg.consolidateNeg map { case Equalities(pos, neg) => Equalities(pos, this.neg ++ neg) }
    else
      Some(this)

  extension (pattern: Pattern) private def asTerm: Term = pattern match
    case Match(ctor, args) => Data(pattern)(ctor, args map { _.asTerm })
    case Bind(ident) => Var(pattern)(ident)

  private def propagatePos: Equalities =
    val propagated = pos map { _ -> propagate(pos, _) match
      case expr0 -> expr1 if expr1 < expr0 => expr1 -> expr0
      case exprs => exprs
    }
    if propagated != pos then
      val normalized = normalize(Map.empty, propagated.iterator) filterNot { _ == _ }
      if normalized != propagated then Equalities(normalized, neg).propagatePos else Equalities(normalized, neg)
    else
      this

  private def propagateNeg: Equalities =
    val propagated = neg map {
      _ map { propagate(pos, _) -> propagate(pos, _) match
        case expr0 -> expr1 if expr1 < expr0 => expr1 -> expr0
        case exprs => exprs
      }
    }
    if propagated != neg then
      val normalized = propagated map { neg => normalize(Map.empty, neg.iterator) }
      if normalized != propagated then Equalities(pos, normalized).propagateNeg else Equalities(pos, normalized)
    else
      this

  private def propagate(pos: Map[Term, Term], expr: Term): Term = pos.getOrElse(expr, expr) match
    case term @ Abs(properties, ident, tpe, expr) =>
      Abs(term)(properties, ident, tpe, propagate(pos, expr))
    case term @ App(properties, expr, arg) =>
      App(term)(properties, propagate(pos, expr), propagate(pos, arg))
    case term @ TypeAbs(ident, expr) =>
      TypeAbs(term)(ident, propagate(pos, expr))
    case term @ TypeApp(expr, tpe) =>
      TypeApp(term)(propagate(pos, expr), tpe)
    case term @ Data(ctor, args) =>
      Data(term)(ctor, args map { propagate(pos, _) })
    case term @ Var(_) =>
      term
    case term @ Cases(scrutinee, cases) =>
      Cases(term)(propagate(pos, scrutinee), cases map { (pattern, expr) => pattern -> propagate(pos, expr) })

  private def consolidateNeg: Option[Equalities] =
    val checkNeg = Equalities(Map.empty, Set.empty)

    Option.when((pos forall { checkNeg.equal(_, _) != Equality.Unequal }) && (neg forall { _.nonEmpty })) {
      val unequalities = neg flatMap { neg =>
        val unequalities = neg filter { checkNeg.equal(_, _) == Equality.Indeterminate }
        Option.when(unequalities.nonEmpty)(unequalities)
      }

      Equalities(pos, unequalities)
    }

  private def normalize(pos: Map[Term, Term], equalities: Iterator[(Term, Term)]) =
    def destruct(expr0: Term, expr1: Term): List[(Term, Term)] = expr0 -> expr1 match
      case App(_, expr0, arg0) -> App(_, expr1, arg1) if equivalent(expr0, expr1) =>
        destruct(arg0, arg1)
      case TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) if equivalent(tpe0, tpe1) =>
        destruct(expr0, expr1)
      case Data(ctor0, args0) -> Data(ctor1, args1) if ctor0 == ctor1 && args0.size == args1.size =>
        args0 zip args1 flatMap destruct
      case exprs =>
        List(exprs)

    def insert(equalities: Map[Term, Term], key: Term, value: Term): Map[Term, Term] =
      destruct(key, value).foldLeft(equalities) { case (equalities, (key, value)) =>
        equalities.get(key) match
          case None =>
            equalities + (key -> value)
          case Some(expr) if expr != value =>
            val otherKey -> otherValue = if expr < value then expr -> value else value -> expr
            insert(equalities + (key -> otherValue), otherKey, otherValue)
          case _ =>
            equalities
      }

    equalities.foldLeft(pos) { case (equalities, (expr0, expr1)) =>
      if expr0 < expr1 then insert(equalities, expr0, expr1) else insert(equalities, expr1, expr0)
    }
end Equalities

object Equalities:
  def empty =
    Equalities(Map.empty, Set.empty)
  def make(pos: IterableOnce[(Term, Term)], neg: IterableOnce[IterableOnce[(Term, Term)]]) =
    empty.withEqualities(pos) flatMap { _.withUnequalities(neg) }
  def pos(pos: IterableOnce[(Term, Term)]) =
    empty.withEqualities(pos)
  def neg(neg: IterableOnce[IterableOnce[(Term, Term)]]) =
    empty.withUnequalities(neg)
