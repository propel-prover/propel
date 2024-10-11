package propel.evaluator.egraph

/** A unique operator. */
trait Operator(override val id: Symbol) extends Element

/** Companion object of [[Operator]]. */
object Operator:
  /**
   * @param name the name of the operator.
   * @return a new [[Operator]] with the specified name.
   */
  def apply(name: String): Operator = BasicOperator(name)

  /** Basic implementation of [[Operator]]. */
  private case class BasicOperator(name: String) extends Operator(Symbol(name))
