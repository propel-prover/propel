package propel
package evaluator
package properties

import ast.*

case class Weight(weight: Int, residuals: Set[Term]) extends PartiallyOrdered[Weight]:
  def tryCompareTo[T >: Weight: [T] =>> T => PartiallyOrdered[T]](that: T) = that match
    case that: Weight =>
      val thisSubsetOfThat = this.residuals.subsetOf(that.residuals)
      val thatSubsetOfThis = that.residuals.subsetOf(this.residuals)
      if thisSubsetOfThat && this.weight < that.weight then Some(-1)
      else if thatSubsetOfThis && that.weight < this.weight then Some(1)
      else if thisSubsetOfThat && thatSubsetOfThis then Some(0)
      else None
    case _ =>
      None

  override def <[T >: Weight: [T] =>> T => PartiallyOrdered[T]](that: T) = (that: @unchecked) match
    case that: Weight => this < that
    case _ => false

  override def >[T >: Weight: [T] =>> T => PartiallyOrdered[T]](that: T) = (that: @unchecked) match
    case that: Weight => this > that
    case _ => false

  inline def <(that: Weight) = this.residuals.subsetOf(that.residuals) && this.weight < that.weight

  inline def >(that: Weight) = that.residuals.subsetOf(this.residuals) && that.weight < this.weight

object Weight:
  def apply(terms: Term*): Weight =
    apply(terms)

  def apply(terms: Iterable[Term]): Weight =
    def weight(terms: Iterable[Term]): (Int, Set[Term]) =
      val (sizes, residuals) =  (terms map {
        case Data(ctor, args) =>
          val (size, residuals) = weight(args)
          (size + 1, residuals)
        case term =>
          (0, Set(term))
      }).unzip
      (sizes.sum, residuals.flatten.toSet)

    val (size, residuals) = weight(terms)
    Weight(size, residuals)
