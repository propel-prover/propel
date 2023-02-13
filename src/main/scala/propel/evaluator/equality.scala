package propel
package evaluator

import ast.*
import typer.*
import util.*

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
  override val hashCode = scala.util.hashing.MurmurHash3.productHash(this)
  override def equals(other: Any) = other match
    case other: Equalities => eq(other) || hashCode == other.hashCode && pos == other.pos && neg == other.neg && other.canEqual(this)
    case _ => false

  def equal(expr0: Term, expr1: Term): Equality =
    def equal(expr0: Term, expr1: Term): (Equality, List[(Term, Term)]) =
      pos.getOrElse(expr0, expr0) -> pos.getOrElse(expr1, expr1) match
        case _ if equivalent(expr0, expr1) =>
          Equality.Equal -> List.empty
        case terms @ App(_, expr0, arg0) -> App(_, expr1, arg1) =>
          equal(expr0, expr1) match
            case Equality.Equal -> _ => equal(arg0, arg1)
            case _ -> _ => Equality.Indeterminate -> List.empty
        case terms @ TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) if equivalent(tpe0, tpe1) =>
          val equality -> exprs = equal(expr0, expr1)
          equality -> (terms :: exprs)
        case terms @ Data(ctor0, args0) -> Data(ctor1, args1) =>
          if ctor0 == ctor1 && args0.sizeCompare(args1) == 0 then
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
                  equal(ne0, expr1) match
                    case (Equality.Equal, _) =>
                      val equality -> _ = equal(ne1, expr0)
                      equality == Equality.Equal
                    case _ =>
                      false
            }
          }
        }
        if unequal then Equality.Unequal else equality
  end equal

  def contradictionIndeducible: Boolean =
    def isVar(expr: Term): Boolean = expr match
      case Var(_) => true
      case _ => false

    def isInductive(expr: Term): Boolean = expr match
      case Var(_) => true
      case Data(_, args) => args forall isInductive
      case _ => false

    def hasSameType(expr0: Term, expr1: Term) =
      expr0.termType exists { tpe => expr1.termType exists { equivalent(tpe, _) } }

    (neg forall { _ forall { (expr0, expr1) => isInductive(expr0) && isInductive(expr1) } }) &&
    (pos forall { (expr0, expr1) =>
      isVar(expr0) || isVar(expr1) ||
      hasSameType(expr0, expr1) && (isInductive(expr0) || isInductive(expr1))
    })
  end contradictionIndeducible

  def withEqualities(equalities: Equalities): Option[Equalities] =
    withEqualities(equalities.pos) flatMap { _.withUnequalities(equalities.neg) }

  def withEqualities(pos: PatternConstraints): Option[Equalities] =
    withEqualities(pos.iterator map { _ -> _.asTerm })

  def withEqualities(pos: (Term, Term)): Option[Equalities] =
    withEqualities(Iterator(pos))

  def withEqualities(pos: IterableOnce[(Term, Term)]): Option[Equalities] =
    val iterator = pos.iterator
    if iterator.nonEmpty then
      normalize(this.pos, homogenize(iterator)) flatMap { pos =>
        Equalities(pos filterNot { _ == _ }, this.neg).propagatePos flatMap { _.propagateNeg.consolidateNeg }
      }
    else
      Some(this)

  def withoutEqualities(pos: (Term, Term)): Equalities =
    withoutEqualities(Iterator(pos))

  def withoutEqualities(pos: IterableOnce[(Term, Term)]): Equalities =
    Equalities(
      pos.iterator.foldLeft(this.pos) {
        case (pos, (expr0, expr1)) if expr1 < expr0 =>
          if pos.get(expr1) contains expr0 then pos - expr1 else pos
        case (pos, (expr0, expr1)) =>
          if pos.get(expr0) contains expr1 then pos - expr0 else pos
      },
      this.neg)

  def withUnequalities(neg: PatternConstraints): Option[Equalities] =
    withUnequalities(List(neg.iterator map { _ -> _.asTerm }))

  def withUnequalities(neg: IterableOnce[IterableOnce[(Term, Term)]]): Option[Equalities] =
    val iterator = neg.iterator
    if iterator.nonEmpty then
      Equalities(this.pos, (iterator flatMap { neg => normalize(Map.empty, homogenize(neg.iterator)) }).toSet)
        .propagateNeg.consolidateNeg map { case Equalities(pos, neg) => Equalities(pos, this.neg ++ neg) }
    else
      Some(this)

  def posConstraints: PatternConstraints =
    val posConstraints = pos flatMap { (expr0, expr1) => expr1.asPattern map { expr0 -> _ } }
    PatternConstraints.make(posConstraints) getOrElse PatternConstraints.empty

  def negConstraints: Set[PatternConstraints] =
    neg flatMap { neg =>
      val negConstraints = neg flatMap { (expr0, expr1) => expr1.asPattern map { expr0 -> _ } }
      if negConstraints.sizeCompare(neg) == 0 then PatternConstraints.make(negConstraints) else None
    }

  extension (pattern: Pattern) private def asTerm: Term = pattern match
    case Match(ctor, args) => Data(pattern)(ctor, args map { _.asTerm })
    case Bind(ident) => Var(pattern)(ident)

  extension (expr: Term) private def asPattern: Option[Pattern] = expr match
    case Data(ctor, args) =>
      val patternArgs = args.foldRight[Option[List[Pattern]]](Some(List.empty)) { (arg, args) =>
        args flatMap { args => arg.asPattern map { _ :: args } }
      }
      patternArgs map { Match(expr)(ctor, _) }
    case _ =>
      None

  def posExpanded: (Map[Term, Term], Map[Term, Term]) =
    val posReverse = pos.foldLeft[Map[Term, Term]](Map.empty) { case (posReverse, (expr0, expr1)) =>
      posReverse + (expr1 -> expr0)
    }

    def expand(expand: (Map[Term, Term], Term) => Iterable[Term]) =
      pos flatMap { case (expr0, expr1) =>
        expand(posReverse, expr0) flatMap { expr =>
          Option.when(expr ne expr0) { if expr1 < expr then expr1 -> expr else expr -> expr1 }
        }
      }

    val expandedAll = expand(propagateAll)

    val expandedSingleLevelVariations = expand(propagateSingleLevelVariations)

    (expandedAll ++ pos, expandedSingleLevelVariations -- expandedAll.keys -- pos.keys)
  end posExpanded

  private def propagatePos: Option[Equalities] =
    val propagatedList = pos.toList mapIfDefined { (expr0, expr1) =>
      propagateAll(pos - expr0, expr0) flatMap { expr0 =>
        propagateAll(pos, expr1) map { expr1 =>
          if expr1 < expr0 then expr1 -> expr0 else expr0 -> expr1
        }
      }
    }

    def process(pos: List[(Term, Term)]): List[(Term, Term)] = pos match
      case Nil => Nil
      case (_: Data, _: Data) :: tail0 => process(tail0)
      case (expr0a, expr1a) :: tail0 =>
        def processTail(pos: List[(Term, Term)]): List[(Term, Term)] = pos match
          case Nil => Nil
          case (_: Data, _: Data) :: tail1 => processTail(tail1)
          case (expr0b, expr1b) :: tail1 =>
            val element0 = (expr0a, expr0b) match
              case (_, _: Data) | (_: Data, _) => Nil
              case element0 @ (expr0a, expr0b)
                  if equivalent(expr0a, expr0b) && equal(expr1a, expr1b) == Equality.Indeterminate =>
                element0 :: Nil
              case _ => Nil
            val element1 = (expr1a, expr1b) match
              case (_, _: Data) | (_: Data, _) => Nil
              case element1 @ (expr1a, expr1b)
                  if equivalent(expr1a, expr1b) && equal(expr0a, expr0b) == Equality.Indeterminate =>
                element1 :: Nil
              case _ => Nil
            element0 ++ element1 ++ processTail(tail1)
        process(tail0) ++ processTail(tail0)

    propagatedList flatMap { propagatedList => 
      val equivalentList = process(propagatedList)

      def iterator = propagatedList.iterator ++ equivalentList.iterator

      if Map.from(iterator) != pos then
        normalize(Map.empty, iterator) flatMap { normalizedPos =>
          val propagatedPos = normalizedPos filterNot { _ == _ }
          if propagatedPos != pos then
            Equalities(propagatedPos, neg).propagatePos
          else
            Some(this)
        }
      else
        Some(this)
    }
  end propagatePos

  private def propagateNeg: Equalities =
    val propagatedList = neg map {
      _.toList flatMap { (expr0, expr1) =>
        propagateAll(pos, expr0) flatMap { expr0 =>
          propagateAll(pos, expr1) map { expr1 =>
            if expr1 < expr0 then expr1 -> expr0 else expr0 -> expr1
          }
        }
      }
    }

    if (propagatedList map { _.toMap }) != neg then
      val propagatedNeg = propagatedList flatMap { neg => normalize(Map.empty, neg.iterator) }
      if propagatedNeg != neg then
        Equalities(pos, propagatedNeg).propagateNeg
      else
        this
    else
      this
  end propagateNeg

  private def propagateAll(pos: Map[Term, Term], expr: Term): Option[Term] =
    def propagate(expr: Term, substituted: Set[Term], boundAnywhere: Set[String]): Option[Term] =
      if !(substituted contains expr) then
        val (propagatedExpr, propagatedSubstituted, propagatedBound) = pos.get(expr) match
          case Some(propagatedExpr) =>
            val syntactic @ (syntacticPropagatedExpr, syntacticInfo) = propagatedExpr.syntactic
            val (convertedExpr, info) =
              if syntacticInfo.freeVars.keys exists { boundAnywhere contains _.name } then
                UniqueNames.convert(expr, boundAnywhere) unwrap { _.syntactic }
              else
                syntactic
            (convertedExpr, substituted + expr, boundAnywhere ++ (info.boundVars map { _.name }))
          case _ =>
            (expr, substituted, boundAnywhere)

        propagatedExpr match
          case term @ Abs(properties, ident, tpe, expr) =>
            propagate(expr, propagatedSubstituted, propagatedBound) map { Abs(term)(properties, ident, tpe, _) }
          case term @ App(properties, expr, arg) =>
            propagate(expr, propagatedSubstituted, propagatedBound) flatMap { expr =>
              propagate(arg, propagatedSubstituted, propagatedBound) map { App(term)(properties, expr, _) }
            }
          case term @ TypeAbs(ident, expr) =>
            propagate(expr, propagatedSubstituted, propagatedBound) map { TypeAbs(term)(ident, _) }
          case term @ TypeApp(expr, tpe) =>
            propagate(expr, propagatedSubstituted, propagatedBound) map { TypeApp(term)(_, tpe) }
          case term @ Data(ctor, args) =>
            args mapIfDefined { propagate(_, propagatedSubstituted, propagatedBound) } map { Data(term)(ctor, _) }
          case term @ Var(_) =>
            Some(term)
          case term @ Cases(scrutinee, cases) =>
            propagate(scrutinee, propagatedSubstituted, propagatedBound) flatMap { scrutinee =>
              (cases
                mapIfDefined { (pattern, expr) =>
                  propagate(expr, propagatedSubstituted, propagatedBound) map { pattern -> _ }
                }
                map { Cases(term)(scrutinee, _) })
            }
      else
        None

    val (syntacticExpr, syntacticInfo) = expr.syntactic
    propagate(syntacticExpr, Set.empty, syntacticInfo.boundVars map { _.name }) map UniformNames.convert
  end propagateAll

  private def propagateSingleLevelVariations(pos: Map[Term, Term], expr: Term): List[Term] =
    val boundAnywhere = expr.syntacticInfo.boundVars map { _.name }

    def propagate(expr: Term): List[Term] =
      val convertedExpr =
        pos.get(expr) map { expr =>
          if expr.syntacticInfo.freeVars.keys exists { boundAnywhere contains _.name } then
            UniqueNames.convert(expr, boundAnywhere).wrapped
          else
            expr
        }

      convertedExpr.toList ++ {
        expr match
          case term @ Abs(properties, ident, tpe, expr) =>
            propagate(expr) map { Abs(term)(properties, ident, tpe, _) }
          case term @ App(properties, expr, arg) =>
            propagate(expr) flatMap { expr =>
              propagate(arg) map { App(term)(properties, expr, _) }
            }
          case term @ TypeAbs(ident, expr) =>
            propagate(expr) map { TypeAbs(term)(ident, _) }
          case term @ TypeApp(expr, tpe) =>
            propagate(expr) map { TypeApp(term)(_, tpe) }
          case term @ Data(ctor, args) =>
            val propagatedArgs = args.foldRight[List[List[Term]]](List(List.empty)) {
              case (arg, args) =>
                propagate(arg) flatMap { arg => { args map { arg :: _ } } }
            }
            propagatedArgs map { Data(term)(ctor, _) }
          case term @ Var(_) =>
            List(term)
          case term @ Cases(scrutinee, cases) =>
            propagate(scrutinee) flatMap { scrutinee =>
              val propagatedCases = cases.foldRight[List[List[(Pattern, Term)]]](List(List.empty)) {
                case (pattern -> expr, cases) =>
                  propagate(expr) flatMap { expr => { cases map { (pattern -> expr) :: _ } } }
              }
              propagatedCases map { Cases(term)(scrutinee, _) }
            }
      }

    propagate(expr) map UniformNames.convert
  end propagateSingleLevelVariations

  private def consolidateNeg: Option[Equalities] =
    val checkNeg = Equalities(Map.empty, Set.empty)
    Option.when((pos forall { checkNeg.equal(_, _) != Equality.Unequal }) && (neg forall { _.nonEmpty })) {
      Equalities(pos, neg filter { _ forall { checkNeg.equal(_, _) != Equality.Unequal } })
    }

  private def homogenize(equalities: Iterator[(Term, Term)]) =
    equalities map { (expr0, expr1) => UniformNames.convert(expr0) -> UniformNames.convert(expr1) }

  private def normalize(pos: Map[Term, Term], equalities: Iterator[(Term, Term)]) =
    def destruct(expr0: Term, expr1: Term): List[(Term, Term)] = expr0 -> expr1 match
      case TypeApp(expr0, tpe0) -> TypeApp(expr1, tpe1) if equivalent(tpe0, tpe1) =>
        destruct(expr0, expr1)
      case Data(ctor0, args0) -> Data(ctor1, args1) if ctor0 == ctor1 && args0.sizeCompare(args1) == 0 =>
        args0 zip args1 flatMap destruct
      case _ if expr1 < expr0 =>
        List(expr1 -> expr0)
      case exprs =>
        List(exprs)

    def insert(equalities: Map[Term, Term], key: Term, value: Term, inserted: Set[Term]): Option[Map[Term, Term]] =
      destruct(key, value).foldLeft[Option[Map[Term, Term]]](Some(equalities)) {
        case (None, _) =>
          None
        case (current @ Some(equalities), (key, value)) =>
          if key != value then
            equalities.get(key) match
              case None =>
                Some(equalities + (key -> value))
              case Some(expr) if expr != value =>
                if !(inserted contains key) then
                  val otherKey -> otherValue = if expr < value then expr -> value else value -> expr
                  insert(equalities + (key -> otherValue), otherKey, otherValue, inserted + key)
                else
                  None
              case _ =>
                current
          else
            current
      }

    equalities.foldLeft[Option[Map[Term, Term]]](Some(pos)) { case (equalities, (expr0, expr1)) =>
      equalities flatMap { equalities =>
        if expr0 < expr1 then insert(equalities, expr0, expr1, Set.empty) else insert(equalities, expr1, expr0, Set.empty)
      }
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
