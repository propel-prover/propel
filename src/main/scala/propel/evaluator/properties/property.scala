package propel
package evaluator
package properties

import ast.*

enum PropertyType:
  case Relation
  case Function

trait PropertyChecking:
  val varA = Var(Symbol("a"))
  val varB = Var(Symbol("b"))
  val varC = Var(Symbol("c"))

  val propertyType: PropertyType

  def prepare(ident0: Symbol, ident1: Symbol, expr: Term): (Term, Equalities)
  def control(expr: Term, equalities: Equalities, nested: Boolean): (Term, Equalities, Symbolic.Control)
  def check(idents: List[Symbol], result: Symbolic.Result): Either[Symbolic.Result, Symbolic.Result]

  protected inline def decreasing(decreasingArguments: DecreasingArguments)(
      firstDecreasing: Boolean,
      arg1Weight: Weight, term1Weight: Weight): Boolean =
    decreasingArguments.first && firstDecreasing || {
      val secondDecreasing = term1Weight < arg1Weight
      decreasingArguments.second && secondDecreasing ||
      decreasingArguments.combined && firstDecreasing && secondDecreasing
    }

  protected inline def decreasing(decreasingArguments: DecreasingArguments)(
      arg0Weight: Weight, term0Weight: Weight,
      secondDecreasing: Boolean): Boolean =
    decreasingArguments.second && secondDecreasing || {
      val firstDecreasing = term0Weight < arg0Weight
      decreasingArguments.first && firstDecreasing ||
      decreasingArguments.combined && firstDecreasing && secondDecreasing
    }

  protected inline def decreasing(decreasingArguments: DecreasingArguments)(
      arg0Weight: Weight, term0Weight: Weight,
      arg1Weight: Weight, term1Weight: Weight): Boolean =
    decreasingArguments.first && term0Weight < arg0Weight ||
    decreasingArguments.second && term1Weight < arg1Weight ||
    decreasingArguments.combined && term0Weight + term1Weight < arg0Weight + arg1Weight

  protected inline def argWeight(arg: Var, equalities: Equalities): Weight =
    Weight(equalities.pos.get(arg) getOrElse arg)

  protected inline def canApply(
      ensureDecreasing: (Property, Term) => Option[DecreasingArguments],
      inline property: Property,
      inline expr: Term)(
      inline canApply: DecreasingArguments => Boolean): Boolean =
    (ensureDecreasing eq PropertyChecking.withNonDecreasing) ||
    (ensureDecreasing(property, expr) forall canApply)

  protected inline def canApply
      (ensureDecreasing: (Property, Term) => Option[DecreasingArguments], equalities: Equalities, property: Property)
      (inline expr: Term)(arg0: Var, term0: Term, arg1: Var, term1: Term): Boolean =
    canApply(ensureDecreasing, property, expr) {
      decreasing(_)(argWeight(arg0, equalities), Weight(term0), argWeight(arg1, equalities), Weight(term1))
    }
end PropertyChecking

object PropertyChecking:
  val withNonDecreasing: (Property, Term) => Option[DecreasingArguments] = (_, _) => None

  trait FunctionEqualResult extends PropertyChecking:
    val propertyType = PropertyType.Function
    val equalDataConstructor = Constructor(Symbol("≟"))

    private def extensional(expr0: Term, expr1: Term): (Term, Term, List[(Term, Term)]) = (expr0, expr1) match
      case (Abs(_, ident0, _, expr0), Abs(_, ident1, _, expr1)) if ident0 < ident1 =>
        val (extensionalExpr0, extensionalExpr1, extensionalEqualities) =
          extensional(expr0, subst(expr1, Map(ident0 -> Var(ident1))))
        (extensionalExpr0, extensionalExpr1, Var(ident0) -> Var(ident1) :: extensionalEqualities)
      case (Abs(_, ident0, _, expr0), Abs(_, ident1, _, expr1)) =>
        val (extensionalExpr0, extensionalExpr1, extensionalEqualities) =
          extensional(expr0, subst(expr1, Map(ident1 -> Var(ident0))))
        (extensionalExpr0, extensionalExpr1, Var(ident1) -> Var(ident0) :: extensionalEqualities)
      case (Abs(_, ident0, _, expr0), expr1) =>
        extensional(expr0, App(Set.empty, expr1, Var(ident0)))
      case (expr0, Abs(_, ident1, _, expr1)) =>
        extensional(App(Set.empty, expr0, Var(ident1)), expr1)
      case (ident0, expr1) =>
        (ident0, expr1, List.empty)

    def control(expr: Term, equalities: Equalities, nested: Boolean) = expr match
      case Data(`equalDataConstructor`, List(arg0, arg1)) if !nested =>
        val (extensionalArg0, extensionalArg1, extensionalEqualities) = extensional(arg0, arg1)
        val control =
          if extensionalArg0 == extensionalArg1 then Symbolic.Control.Stop
          else if equalities.equal(extensionalArg0, extensionalArg1) == Equality.Unequal &&
                  equalities.contradictionIndeducible then Symbolic.Control.Terminate
          else Symbolic.Control.Continue
        (Data(expr)(`equalDataConstructor`, List(extensionalArg0, extensionalArg1)),
         Equalities.pos(extensionalEqualities) getOrElse Equalities.empty,
         control)
      case _ =>
        (expr, Equalities.empty, Symbolic.Control.Continue)

    def check(idents: List[Symbol], result: Symbolic.Result) =
      val unproven = Symbolic.Result(result.reductions filterNot {
        case Symbolic.Reduction(Data(`equalDataConstructor`, List(arg0, arg1)), _, _) => arg0 == arg1
        case _ => false
      })
      val disproved = unproven.reductions exists {
        case Symbolic.Reduction(Data(`equalDataConstructor`, List(arg0, arg1)), _, equalities) =>
          equalities.equal(arg0, arg1) == Equality.Unequal && equalities.contradictionIndeducible
        case _ =>
          false
      }
      Either.cond(!disproved, unproven, unproven)

  trait FunctionSelectionResult extends PropertyChecking:
    val propertyType = PropertyType.Function
    val resultDataConstructor = Constructor(Symbol("≛"))

    def control(expr: Term, equalities: Equalities, nested: Boolean) =
      (expr, Equalities.empty, Symbolic.Control.Continue)

    def check(idents: List[Symbol], result: Symbolic.Result) =
      val unproven = Symbolic.Result(result.reductions filterNot {
        case Symbolic.Reduction(Data(`resultDataConstructor`, List(arg)), _, equalities) =>
          idents exists { ident => equalities.equal(arg, Var(ident)) == Equality.Equal }
        case _ =>
          false
      })
      val disproved = unproven.reductions exists {
        case Symbolic.Reduction(Data(`resultDataConstructor`, List(arg)), _, equalities) =>
          (idents forall { ident => equalities.equal(arg, Var(ident)) == Equality.Unequal }) && equalities.contradictionIndeducible
        case _ =>
          false
      }
      Either.cond(!disproved, unproven, unproven)

  trait RelationTrueResult extends PropertyChecking:
    val propertyType = PropertyType.Relation

    def control(expr: Term, equalities: Equalities, nested: Boolean) =
      val control =
        if nested then Symbolic.Control.Continue
        else if expr == Data(Constructor.True, List()) then Symbolic.Control.Stop
        else if equalities.equal(expr, Data(Constructor.True, List())) == Equality.Unequal &&
                equalities.contradictionIndeducible then Symbolic.Control.Terminate
        else Symbolic.Control.Continue
      (expr, Equalities.empty, control)

    def check(idents: List[Symbol], result: Symbolic.Result) =
      val unproven = Symbolic.Result(result.reductions filterNot {
        case Symbolic.Reduction(Data(Constructor.True, List()), _, _) => true
        case _ => false
      })
      val disproved = unproven.reductions exists {
        case Symbolic.Reduction(expr, _, equalities) =>
          equalities.equal(expr, Data(Constructor.True, List())) == Equality.Unequal && equalities.contradictionIndeducible
      }
      Either.cond(!disproved, unproven, unproven)

  trait Simple extends PropertyChecking:
    def deriveSimple(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities): PartialFunction[(Term, Term), List[Equalities]]

  trait Compound extends PropertyChecking:
    def deriveCompound(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities): PartialFunction[((Term, Term), (Term, Term)), List[Equalities]]

  trait Normal extends PropertyChecking:
    def normalize(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities): PartialFunction[Term, Term]

  trait Selecting extends PropertyChecking:
    def select(ensureDecreasing: (Property, Term) => Option[DecreasingArguments])(equalities: Equalities): PartialFunction[Term, List[(Term, Equalities)]]
end PropertyChecking
