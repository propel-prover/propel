package propel.evaluator.egraph

/** An equivalence class representing a set containing equivalent [[Element]]s. */
trait EClass extends Element:
  /** @return the [[ENode]] representative of this [[EClass]]. */
  def canonical: ENode

/** Companion object of [[EClass]]. */
object EClass:
  /** The machine-identifier of an [[EClass]]. */
  type Id = Element.Id

  /**
   * @param canonical the specified [[ENode]], representative of this [[EClass]].
   * @return a new [[EClass]] representing an equivalence class containing the
   *         specified [[ENode]].
   */
  def apply(canonical: ENode): EClass = BasicEClass(canonical)

  /** Basic implementation of [[EClass]]. */
  private case class BasicEClass(override val canonical: ENode) extends EClass:
    override final lazy val id: Symbol = canonical.id