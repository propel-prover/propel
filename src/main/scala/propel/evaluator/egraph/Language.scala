package propel.evaluator.egraph

import propel.ast.Pattern.{Bind, Match}
import propel.ast.Term.{Abs, App, Cases, Data, TypeAbs, TypeApp, Var}
import propel.ast.{Pattern, Term, Type}

/**
 * A language for writing terms interpretable by e-graphs.
 * @tparam T the possible terms in the language.
 * @note a language depends on a [[EClassGenerator]] to generate [[EClass]]es and
 *       [[ENode]] from terms. Most of the time, this dependency is actually the
 *       e-graph to which the language is being adapted. Maybe there is a better
 *       way to specify this dependency.
 */
trait Language[T]:
  /** An implicit [[Conversion]] from terms to [[ENode]]s. */
  given termAsEnode(using EClassGenerator): Conversion[T, ENode] = this.parse
  /** An implicit [[Conversion]] from terms to [[EClass]]es. */
  given termAsEClass(using EClassGenerator): Conversion[T, EClass] = this.parseClass

  /**
   * @param term the specified term.
   * @param generator a function generating [[EClass]]es from [[ENode]]s.
   * @return the [[ENode]] corresponding to the specified term.
   */
  def parse(term: T)(using generator: EClassGenerator): ENode
  /**
   * @param term the specified term.
   * @param generator a function generating [[EClass]]es from [[ENode]]s.
   * @return the [[EClass]] corresponding to the specified term.
   */
  def parseClass(term: T)(using generator: EClassGenerator): EClass = generator(this.parse(term))
    
/** Companion object of [[Language]]. */
object Language:
  /** An adapter from the language of propel to the language of e-graphs. */
  object PropelLanguage:
    /** The set of [[Operator]]s in propel. */
    object Operators:
      def Type: Operator = op(":")
      def Lambda: Operator = op("λ")
      def TypeLambda(domain: Symbol): Operator = op(s"Λ${domain.name}")
      def Application: Operator = op("apply")
      def TypeApplication: Operator = op("applyType")
      def Constructor: Operator = op("new")
      def Match: Operator = op("match")
      def Case: Operator = op("case")
      private inline def op(name: String): Operator = Operator(s"@$name")

  trait PropelLanguage extends Language[propel.ast.Term]:
    override def parse(term: Term)(using generator: EClassGenerator): ENode = term match
      case Abs(properties, ident, tpe, expr) =>
        ENode(PropelLanguage.Operators.Lambda, Seq(
          this.parseClass(ident),
          this.parseClass(expr)
        ))
      case TypeAbs(ident, expr) =>
        ENode(PropelLanguage.Operators.TypeLambda(ident), Seq(
          this.parseClass(expr)
        ))
      case App(properties, expr, arg) =>
        ENode(PropelLanguage.Operators.Application, Seq(
          this.parseClass(expr),
          this.parseClass(arg)
        ))
      case TypeApp(expr, tpe) =>
        ENode(PropelLanguage.Operators.TypeApplication, Seq(
          this.parseClass(expr),
          this.parseClass(tpe)
        ))
      case Data(ctor, args) =>
        ENode(Operator(ctor.ident.name), args.map(this.parseClass))
      case Var(ident) =>
        ENode(Operator(ident.name))
      case Cases(scrutinee, cases) =>
        ENode(PropelLanguage.Operators.Match,
          this.parseClass(scrutinee) +:
          cases.map((pattern, term) => generator(
            ENode(PropelLanguage.Operators.Case, Seq(
              this.parseClass(pattern),
              this.parseClass(term)
            ))
          ))
        )

    private def parseClass(id: Symbol)(using generator: EClassGenerator): EClass =
      generator(ENode(Operator(id.name)))
      
    private def parseClass(tpe: Type)(using generator: EClassGenerator): EClass =
      this.parseClass(Symbol(tpe.toString))
      
    private def parseClass(pattern: Pattern)(using generator: EClassGenerator): EClass = pattern match
      case Match(ctor, args) =>
        generator(ENode(Operator(ctor.ident.name), args.map(this.parseClass)))
      case Bind(ident) =>
        this.parseClass(Symbol(s"?${ident.name}"))