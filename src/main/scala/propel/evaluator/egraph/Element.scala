package propel.evaluator.egraph

/** A unique element in the universal set. */
trait Element:
  /** @return the identifier of this [[Element]]. */
  def id: Element.Id
  override def toString: String = this.id.name

/** Companion object of [[Element]]. */
object Element:
  /** The machine-identifier of an [[Element]]. */
  type Id = Symbol