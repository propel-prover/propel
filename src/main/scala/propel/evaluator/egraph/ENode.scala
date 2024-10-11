package propel.evaluator.egraph

/** A node representing an [[Operator]] applied to [[EClass]]es. */
trait ENode extends Element:
  /** @return the [[Operator]] applied by this [[ENode]]. */
  def op: Operator
  /** @return the [[EClass]] to which [[op]] is applied. */
  def refs: Seq[EClass]
  
/** Companion object of [[ENode]]. */
object ENode:
  /** The machine-identifier of an [[ENode]]. */
  type Id = Element.Id

  /**
   * @param op the specified [[Operator]].
   * @param refs the specified [[EClass]]es.
   * @return a new [[ENode]] representing the specified [[Operator]] applied to the specified [[EClass]]es.
   */
  def apply(op: Operator, refs: Seq[EClass] = Seq()): ENode =
    BasicENode(op, refs)

  /** Basic implementation of [[ENode]]. */
  private case class BasicENode(override val op: Operator, override val refs: Seq[EClass]) extends ENode:
    override final lazy val id: Symbol = Symbol({
      val refsString: String = this.refs.mkString(",")
      s"$op${if refsString.nonEmpty then s"($refsString)" else ""}"
    })
