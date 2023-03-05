package propel
package evaluator
package properties

import ast.*

case class Weight(weight: Int, residuals: List[Term]) extends PartiallyOrdered[Weight]:
  def tryCompareTo[T >: Weight: [T] =>> T => PartiallyOrdered[T]](that: T) = that match
    case that: Weight =>
      val thisSubsetOfThat = subMultisetOf(this.residuals, that.residuals)
      val thatSubsetOfThis = subMultisetOf(that.residuals, this.residuals)
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

  inline def <(that: Weight) = subMultisetOf(this.residuals, that.residuals) && this.weight < that.weight

  inline def >(that: Weight) = subMultisetOf(that.residuals, this.residuals) && that.weight < this.weight

  private def subMultisetOf(self: List[Term], other: List[Term]): Boolean =
    def remove(elem: Term, list: List[Term]): List[Term] =
      if list.isEmpty then list
      else
        val tail = list.tail
        if list.head == elem then tail
        else
          val rest = remove(elem, tail)
          if rest eq tail then list
          else list.head :: rest

    if self.isEmpty then true
    else
      val removed = remove(self.head, other)
      if removed eq other then false
      else subMultisetOf(self.tail, removed)


object Weight:
  def apply(terms: Term*): Weight =
    apply(terms)

  def apply(terms: Iterable[Term]): Weight =
    def weight(terms: Iterable[Term]): (Int, List[Term]) =
      val (sizes, residuals) =  (terms map {
        case Data(ctor, args) =>
          val (size, residuals) = weight(args)
          (size + 1, residuals)
        case term =>
          (0, List(term))
      }).unzip
      (sizes.sum, residuals.flatten.toList)

    val (size, residuals) = weight(terms)
    Weight(size, residuals)
