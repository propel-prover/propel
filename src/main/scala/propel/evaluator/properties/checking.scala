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

  val typedExpr = expr.typedTerm

  val abstractionProperties: Map[Abstraction, Properties] =
    def abstractionProperties(term: Term): Map[Abstraction, Properties] = term match
      case Abs(properties, _, _, expr) =>
        term.info(Abstraction) map { abstraction =>
          abstractionProperties(expr) + (abstraction -> properties)
        } getOrElse abstractionProperties(expr)
      case App(_, expr, arg) => abstractionProperties(expr) ++ abstractionProperties(arg)
      case TypeAbs(_, expr) => abstractionProperties(expr)
      case TypeApp(expr, _) => abstractionProperties(expr)
      case Data(_, args) => (args flatMap abstractionProperties).toMap
      case Var(ident) => Map.empty
      case Cases(scrutinee, cases) =>
        abstractionProperties(scrutinee) ++ (cases flatMap { (_, expr) =>
          abstractionProperties(expr)
        })
    abstractionProperties(typedExpr)

  def typedVar(ident: Symbol, tpe: Option[Type]) = tpe match
    case Some(tpe) =>
      val expr = Var(ident).withExtrinsicInfo(Typing.Specified(Right(tpe)))
      tpe.info(Abstraction) map { expr.withExtrinsicInfo(_) } getOrElse expr
    case _ =>
      Var(ident)

  def typedArgVar(ident: Symbol, tpe: Option[Type]) =
     typedVar(ident, tpe collect { case Function(arg, _) => arg })

  def typedBindings(pattern: Pattern): Map[Symbol, Term] = pattern match
    case Match(_, args) => (args flatMap typedBindings).toMap
    case Bind(ident) => Map(ident -> typedVar(ident, pattern.patternType))

  var collectedNormalizations = List.empty[(Abstraction => Option[Term]) => Option[Equalities => PartialFunction[Term, Term]]]

  def check(term: Term, env: Map[Symbol, Term]): Term = term match
    case Abs(properties, ident0, tpe0, expr0 @ Abs(_, ident1, tpe1, expr1)) =>
      if printReductionDebugInfo || printDeductionDebugInfo then
        if debugInfoPrinted then
          println()
        else
          debugInfoPrinted = true
        println("Checking properties for definition:")
        println()
        println(indent(2, term.show))

      val names = env.keys map { _.name }

      val abstractions = env flatMap { (_, expr) => expr.info(Abstraction) map { _ -> expr } }

      val collectedNormalize = collectedNormalizations flatMap { _(abstractions.get) }

      val (abstraction, call) = (term.info(Abstraction), recursiveCalls(term)) match
        case (abstraction @ Some(_), call :: _) => (abstraction, Some(call))
        case _ => (None, None)

      val converted = UniqueNames.convert(expr1, names)
      val result = Symbolic.eval(converted)

      val facts = Conjecture.basicFacts(properties, term, ident0, ident1, result)

      val normalizeFacts =
        if call.nonEmpty then
          facts map { fact =>
            fact.checking(
              call.get,
              _ forall { _.info(Abstraction) contains abstraction.get },
              _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                val abstraction = expr.info(Abstraction)
                abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
              } },
              (fact.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap).normalize
          }
        else
          List.empty

      val conjectures =
        if call.nonEmpty then
          val distributivityConjectures =
            if expr1.termType exists { equivalent(tpe0, _) } then
              val tpe = Function(tpe0, Function(tpe0, tpe0))
              (expr1.syntacticInfo.freeVars.keySet collect {
                case ident if env.get(ident) exists { _.termType exists { equivalent(tpe, _) } } =>
                  val identProperties = env(ident).info(Abstraction) flatMap abstractionProperties.get getOrElse Set.empty

                  def side0(properties0: Properties, ident0: Symbol, properties1: Properties, ident1: Symbol) = App(Set.empty,
                    App(properties0, Var(ident0), Var(Symbol("a"))),
                    App(Set.empty, App(properties1, Var(ident1), Var(Symbol("b"))), Var(Symbol("c"))))

                  def side1(properties0: Properties, ident0: Symbol, properties1: Properties, ident1: Symbol) = App(Set.empty,
                    App(properties1, Var(ident1), App(Set.empty, App(properties0, Var(ident0), Var(Symbol("a"))), Var(Symbol("b")))),
                    App(Set.empty, App(properties0, Var(ident0), Var(Symbol("a"))), Var(Symbol("c"))))

                  def normalization(side0: Term, side1: Term) =
                    Normalization(side0, side1, Symbol("∘"), None, Set(Symbol("a"), Symbol("b"), Symbol("c")))

                  List(
                    normalization(
                      side0(properties, Symbol("∘"), identProperties, ident),
                      side1(properties, Symbol("∘"), identProperties, ident)),
                    normalization(
                      side1(properties, Symbol("∘"), identProperties, ident),
                      side0(properties, Symbol("∘"), identProperties, ident)),
                    normalization(
                      side0(identProperties, ident, properties, Symbol("∘")),
                      side1(identProperties, ident, properties, Symbol("∘"))),
                    normalization(
                      side1(identProperties, ident, properties, Symbol("∘")),
                      side0(identProperties, ident, properties, Symbol("∘"))))
              }).flatten.toList
            else
              List.empty

          distributivityConjectures ++ Conjecture.generalizedConjectures(properties, term, ident0, ident1, tpe0, result) filterNot {
            Normalization.specializationForSameAbstraction(_, facts)
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
          val checking = conjecture.checking(
            call.get,
            _ forall { _.info(Abstraction) contains abstraction.get },
            _ forall { (ident, exprs) => env.get(ident) exists { expr =>
              val abstraction = expr.info(Abstraction)
              abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
            } },
            (conjecture.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap)
          val normalizeConjecture = checking.normalize

          val (expr, equalities) = checking.prepare(ident0, ident1, expr1)
          val converted = UniqueNames.convert(expr, names)

          if printReductionDebugInfo then
            println()
            println(indent(2, s"Checking conjecture: ${conjecture.show}"))
            println()
            println(indent(4, converted.wrapped.show))

          val config = Symbolic.Configuration(
            evaluator.properties.normalize(normalizeFacts ++ (normalizeConjecture :: normalizeConjectures ++ collectedNormalize ++ normalizing), _, _),
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
            remaining filterNot { Normalization.specializationForSameAbstraction(_, proven) },
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
                if Normalization.equivalentForSameAbstraction(property, propertyHead) then
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
          filterNot { (property, _) =>
            Normalization.specializationForSameAbstraction(property, distinctProperties filterNot { _ eq property })
          }
          sortBy { case Normalization(pattern, result, _, _, _) -> _ =>
            (pattern, result)
          }).unzip

      abstraction foreach { abstraction =>
        collectedNormalizations ++= provenProperties map { property => exprs =>
          exprs(abstraction) map { expr =>
            val freeExpr = (property.free flatMap { ident =>
              env.get(ident) flatMap { _.info(Abstraction) flatMap exprs map { ident -> _ } }
            }).toMap

            property.checking(
              expr,
              _ forall { _.info(Abstraction) contains abstraction },
              _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                val abstraction = expr.info(Abstraction)
                abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
              } },
              freeExpr).normalize
          }
        }
      }

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
              val converted = UniqueNames.convert(expr, names)

              if printReductionDebugInfo then
                println()
                println(indent(2, s"Checking ${property.show} property:"))
                println()
                println(indent(4, converted.wrapped.show))

              val config = Symbolic.Configuration(
                evaluator.properties.normalize(normalize ++ collectedNormalize ++ normalizing, _, _),
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
        case _ => Abs(term)(properties, ident0, tpe0, check(expr0, env + (ident0 -> typedArgVar(ident0, term.termType))))
    case Abs(properties, ident, tpe, expr) =>
      if properties.nonEmpty then
        term.withExtrinsicInfo(illshapedDefinitionError(properties.head))
      else
        Abs(term)(properties, ident, tpe, check(expr, env + (ident -> typedArgVar(ident, term.termType))))
    case App(properties, expr, arg) =>
      App(term)(properties, check(expr, env), check(arg, env))
    case TypeAbs(ident, expr) =>
      TypeAbs(term)(ident, check(expr, env))
    case TypeApp(expr, tpe) =>
      TypeApp(term)(check(expr, env), tpe)
    case Data(ctor, args) =>
      Data(term)(ctor, args map { check(_, env) })
    case Var(_) =>
      expr
    case Cases(scrutinee, cases) =>
      Cases(term)(check(scrutinee, env), cases map { (pattern, expr) => pattern -> check(expr, env ++ typedBindings(pattern)) })

  if typedExpr.termType.isDefined then
    check(typedExpr, Map.empty)
  else
    typedExpr
end check
