package propel
package evaluator
package properties

import ast.*
import printing.*
import typer.*
import util.*

def check(expr: Term, printDeductionDebugInfo: Boolean = false, printReductionDebugInfo: Boolean = false): Term =
  var debugInfoPrinted = false

  def indent(indentation: Int, string: String) =
    val indent = " " * indentation
    (string.linesIterator map { line => if line.nonEmpty then s"$indent$line" else line }).mkString(s"${System.lineSeparator}")

  val boolType = Sum(List(Constructor.True -> List.empty, Constructor.False -> List.empty))
  val relationType = Function(TypeVar(Symbol("T")), Function(TypeVar(Symbol("T")), boolType))
  val functionType = Function(TypeVar(Symbol("T")), Function(TypeVar(Symbol("T")), TypeVar(Symbol("T"))))
  val definition =
    Abs(Set.empty, Symbol(s"v${Naming.subscript(0)}"), TypeVar(Symbol("T")),
      Abs(Set.empty, Symbol(s"v${Naming.subscript(1)}"), TypeVar(Symbol("T")), Var(Symbol("e"))))

  def unknownPropertyError(property: Property) = Error(
    s"Property Deduction Error\n\nUnable to check ${property.show} property.")
  def illformedRelationTypeError(property: Property, tpe: Option[Type]) = Error(
    s"Property Deduction Error\n\nExpected relation type of shape ${relationType.show} to check ${property.show} property${
      if tpe.nonEmpty then s" but found ${tpe.get.show}." else "."
    }")
  def illformedFunctionTypeError(property: Property, tpe: Option[Type]) = Error(
    s"Property Deduction Error\n\nExpected function type of shape ${functionType.show} to check ${property.show} property${
      if tpe.nonEmpty then s" but found ${tpe.get.show}." else "."
    }")
  def illshapedDefinitionError(property: Property) = Error(
    s"Property Deduction Error\n\nExpected function definition of shape ${definition.show} to check ${property.show} property.")
  def propertyDeductionError(property: Property) = Error(
    s"Property Deduction Error\n\nUnable to prove ${property.show} property.")

  def specialization(special: Normalization, general: Iterable[Normalization]) =
    def specialization(special: Normalization, general: Normalization, specialExpr: Term, generalExpr: Term) =
      Unification.unify(generalExpr, specialExpr) exists { (generalConstraints, specialConstraints) =>
        specialConstraints.isEmpty &&
        (general.idents forall { ident =>
          generalConstraints.get(ident) collect { case Var(ident) => ident } forall { special.idents contains _ }
        })
      }

    general exists { general =>
      specialization(special, general, special.pattern, general.pattern) &&
      specialization(special, general, special.result, general.result) &&
      (special.form.isEmpty && general.form.isEmpty ||
        (special.form exists { form => general.form exists { !Unification.refutable(_, form) } }))
    }

  def check(term: Term): Term = term match
    case Abs(properties, ident0, tpe0, expr0 @ Abs(_, ident1, tpe1, expr1)) =>
      if printReductionDebugInfo || printDeductionDebugInfo then
        if debugInfoPrinted then
          println()
        else
          debugInfoPrinted = true
        println("Checking properties for definition:")
        println()
        println(indent(2, term.show))

      val (abstraction, call) = (term.info(Abstraction), recursiveCall(term)) match
        case some @ (Some(_), Some(_)) => some
        case _ => (None, None)

      val converted = UniqueNames.convert(expr1)
      val result = Symbolic.eval(converted)

      val facts = Conjecture.basicFacts(properties, term, ident0, ident1, result)

      val normalizeFacts =
        if call.nonEmpty then
          facts map { _.checking(_ forall { _.info(Abstraction) contains abstraction.get }, call.get).normalize }
        else
          List.empty

      val conjectures =
        if call.nonEmpty then
          val config = Symbolic.Configuration(
            evaluator.properties.normalize(normalizeFacts ++ normalizing, _, _),
            evaluator.properties.derive)
          Conjecture.generalizedConjectures(properties, term, ident0, ident1, tpe0, result) filterNot {
            specialization(_, facts)
          }
        else
          List.empty

      if printDeductionDebugInfo then
        if call.isEmpty then
          println()
          println(indent(2, "No known recursion scheme detected."))

        if facts.nonEmpty then
          println()
          println(indent(2, "Basic facts:"))
          println()
          facts map { fact => println(indent(4, fact.show)) }

        if conjectures.nonEmpty then
          println()
          println(indent(2, "Generalized conjectures:"))
          println()
          conjectures map { conjecture => println(indent(4, conjecture.show)) }

      def proveConjectures(
          conjectures: List[Normalization],
          provenConjectures: List[Normalization] = List.empty,
          normalizeConjectures: List[Equalities => PartialFunction[Term, Term]] = List.empty)
      : (List[Normalization], List[Equalities => PartialFunction[Term, Term]]) =

        val (remaining, additional) = conjectures partitionMap { conjecture =>
          val checking = conjecture.checking(_ forall { _.info(Abstraction) contains abstraction.get }, call.get)
          val normalizeConjecture = checking.normalize

          val (expr, equalities) = checking.prepare(ident0, ident1, expr1)
          val converted = UniqueNames.convert(expr)

          if printReductionDebugInfo then
            println()
            println(indent(2, s"Checking conjecture: ${conjecture.show}"))
            println()
            println(indent(4, converted.wrapped.show))

          val config = Symbolic.Configuration(
            evaluator.properties.normalize(normalizeFacts ++ (normalizeConjecture :: normalizeConjectures ++ normalizing), _, _),
            evaluator.properties.derive)

          val result = Symbolic.eval(converted, equalities, config)

          if printReductionDebugInfo then
            println()
            println(indent(2, "Evaluation result for conjecture check:"))
            println()
            println(indent(4, result.wrapped.show))

          val successful = checking.check(result.wrapped)

          if printReductionDebugInfo then
            println()
            if successful then
              println(indent(4, "✔ Conjecture proven".toUpperCase.nn))
            else
              println(indent(4, "✘ Conjecture could not be proven".toUpperCase.nn))

          Either.cond(successful, conjecture -> normalizeConjecture, conjecture)
        }

        val (proven, normalize) = additional.unzip

        if remaining.isEmpty || additional.isEmpty then
          (provenConjectures ++ proven, normalizeConjectures ++ normalize)
        else
          proveConjectures(
            remaining filterNot { specialization(_, proven) },
            provenConjectures ++ proven,
            normalizeConjectures ++ normalize)
      end proveConjectures

      val (provenConjectures, normalizeConjectures) = proveConjectures(conjectures)

      val (provenProperties, normalize) =
        type Properties = List[(Normalization, Equalities => PartialFunction[Term, Term])]

        def distinct(properties: Properties): Properties = properties match
          case Nil => Nil
          case (head @ (propertyHead, _)) :: tail =>
            def distinctTail(properties: Properties): Properties = properties match
              case Nil => Nil
              case (head @ (property, _)) :: tail =>
                if specialization(property, List(propertyHead)) &&
                   specialization(propertyHead, List(property)) then
                  distinctTail(tail)
                else
                  head :: distinctTail(tail)
            head :: distinct(distinctTail(tail))

        val properties = facts ++ provenConjectures

        val normalize =
          val normalize = normalizeFacts ++ normalizeConjectures
          if normalize.isEmpty then List.fill(properties.size)((_: Equalities) => PartialFunction.empty)
          else normalize

        val distinctPropertiesNormalize = distinct(properties zip normalize)
        val (distinctProperties, _) = distinctPropertiesNormalize.unzip
        (distinctPropertiesNormalize
          filterNot { (property, _) => specialization(property, distinctProperties filterNot { _ eq property }) }
          sortBy { case Normalization(pattern, result, _, _) -> _ => (pattern, result) }).unzip

      if printDeductionDebugInfo && provenProperties.nonEmpty then
        println()
        println(indent(2, "Proven properties:"))
        println()
        provenProperties map { property => println(indent(4, property.show)) }

      val error = properties collectFirstDefined { property =>
        propertiesChecking get property match
          case None =>
            Some(unknownPropertyError(property))
          case Some(checking) =>
            if checking.propertyType == PropertyType.Relation &&
               (!equivalent(tpe0, tpe1) || (expr1.termType forall { !equivalent(boolType, _) })) then
              Some(illformedRelationTypeError(property, term.termType))
            else if checking.propertyType == PropertyType.Function &&
               (!equivalent(tpe0, tpe1) || (expr1.termType forall { !equivalent(tpe0, _) })) then
              Some(illformedFunctionTypeError(property, term.termType))
            else
              val (expr, equalities) = checking.prepare(ident0, ident1, expr1)
              val converted = UniqueNames.convert(expr)

              if printReductionDebugInfo then
                println()
                println(indent(2, s"Checking ${property.show} property:"))
                println()
                println(indent(4, converted.wrapped.show))

              val config = Symbolic.Configuration(
                evaluator.properties.normalize(normalize ++ normalizing, _, _),
                evaluator.properties.derive)

              val result = Symbolic.eval(converted, equalities, config)

              if printReductionDebugInfo then
                println()
                println(indent(2, s"Evaluation result for ${property.show} property check:"))
                println()
                println(indent(4, result.wrapped.show))

              val successful = checking.check(result.wrapped)

              if printReductionDebugInfo || printDeductionDebugInfo then
                println()
                if successful then
                  println(indent(4, s"✔ ${property.show} property proven".toUpperCase.nn))
                else
                  println(indent(4, s"✘ ${property.show} property could not be proven".toUpperCase.nn))

              Option.when(!successful)(propertyDeductionError(property))
      }
      error match
        case Some(error) => term.withExtrinsicInfo(error)
        case _ => Abs(term)(properties, ident0, tpe0, check(expr0))
    case Abs(properties, ident, tpe, expr) =>
      if properties.nonEmpty then
        term.withExtrinsicInfo(illshapedDefinitionError(properties.head))
      else
        Abs(term)(properties, ident, tpe, check(expr))
    case App(properties, expr, arg) =>
      App(term)(properties, check(expr), check(arg))
    case TypeAbs(ident, expr) =>
      TypeAbs(term)(ident, check(expr))
    case TypeApp(expr, tpe) =>
      TypeApp(term)(check(expr), tpe)
    case Data(ctor, args) =>
      Data(term)(ctor, args map check)
    case Var(_) =>
      expr
    case Cases(scrutinee, cases) =>
      Cases(term)(check(scrutinee), cases map { (pattern, expr) => pattern -> check(expr) })

  expr.typed match
    case expr -> Some(_) => check(expr)
    case expr -> _ => expr
end check
