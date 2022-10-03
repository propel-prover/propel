package propel
package evaluator
package properties

import ast.*
import printing.*
import typer.*
import util.*

def check(expr: Term, assumedConjectures: List[Normalization] = List.empty, printDeductionDebugInfo: Boolean = false, printReductionDebugInfo: Boolean = false): Term =
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
  def propertyDisprovenError(property: Property) = Error(
    s"Property Deduction Error\n\nDisproved ${property.show} property.")

  val typedExpr = expr.typedTerm

  val (abstractionProperties, abstractionResultTypes) =
    def abstractionPropertiesResultTypes(term: Term): Map[Abstraction, (Properties, Type)] = term match
      case Abs(properties, _, _, expr) =>
        term.info(Abstraction) flatMap { abstraction =>
          expr.termType map { tpe =>
            abstractionPropertiesResultTypes(expr) + (abstraction -> (properties, tpe))
          }
        } getOrElse abstractionPropertiesResultTypes(expr)
      case App(_, expr, arg) => abstractionPropertiesResultTypes(expr) ++ abstractionPropertiesResultTypes(arg)
      case TypeAbs(_, expr) => abstractionPropertiesResultTypes(expr)
      case TypeApp(expr, _) => abstractionPropertiesResultTypes(expr)
      case Data(_, args) => (args flatMap abstractionPropertiesResultTypes).toMap
      case Var(ident) => Map.empty
      case Cases(scrutinee, cases) =>
        abstractionPropertiesResultTypes(scrutinee) ++ (cases flatMap { (_, expr) =>
          abstractionPropertiesResultTypes(expr)
        })

    val propertiesResultTypes = abstractionPropertiesResultTypes(typedExpr)
    (propertiesResultTypes.view mapValues { (properties, _) => properties }).toMap ->
    (propertiesResultTypes.view mapValues { (_, tpe) => tpe }).toMap

  def typeContradiction(abstraction: Term, expr: Term) =
    abstraction.info(Abstraction) exists { abstraction =>
      abstractionResultTypes.get(abstraction) exists { tpe =>
        expr.termType exists { !conforms(_, tpe) }
      }
    }

  def deriveTypeContradiction(equalities: Equalities): PartialFunction[(Term, Term), List[Equalities]] =
    case (App(_, abstraction, _), expr) if typeContradiction(abstraction, expr) =>
      Equalities.pos(List(Data(Constructor.False, List.empty) -> Data(Constructor.True, List.empty))).toList
    case (expr, App(_, abstraction, _)) if typeContradiction(abstraction, expr) =>
      Equalities.pos(List(Data(Constructor.False, List.empty) -> Data(Constructor.True, List.empty))).toList

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

  def addCollectedNormalizations(env: Map[Symbol, Term], abstraction: Option[Abstraction], normalizations: List[Normalization]) =
    abstraction foreach { abstraction =>
      collectedNormalizations ++= normalizations map { property => exprs =>
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

  def exprArgumentPrefixes(expr: Term): List[(List[Symbol], Term)] = expr match
    case Abs(_, ident, _, expr) =>
      List(ident) -> expr :: (exprArgumentPrefixes(expr) map { (idents, expr) => (ident :: idents) -> expr })
    case _ =>
      List.empty

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

      val result = Symbolic.eval(UniqueNames.convert(expr1, names))

      val facts = exprArgumentPrefixes(term) flatMap { (idents, expr) =>
        val evaluationResult =
          if expr ne expr1 then
            Symbolic.eval(UniqueNames.convert(expr, names))
          else
            result
        Conjecture.basicFacts(properties, term, idents, evaluationResult)
      }

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
          val closedBinaryOperation = expr1.termType exists { equivalent(tpe0, _) }

          val unaryDistributivityConjectures =
            if closedBinaryOperation then
              val tpe = Function(tpe0, tpe0)
              (expr1.syntacticInfo.freeVars.keySet.toList.sorted collect {
                case ident if env.get(ident) exists { _.termType exists { equivalent(tpe, _) } } =>
                  val identProperties = env(ident).info(Abstraction) flatMap abstractionProperties.get getOrElse Set.empty

                  val side0 = App(identProperties, Var(ident),
                    App(Set.empty, App(properties, Var(Symbol("∘")), Var(Symbol("a"))), Var(Symbol("b"))))

                  val side1a = App(Set.empty,
                    App(properties, Var(Symbol("∘")), App(identProperties, Var(ident), Var(Symbol("a")))), Var(Symbol("b")))

                  val side1b = App(Set.empty,
                    App(properties, Var(Symbol("∘")), Var(Symbol("a"))), App(identProperties, Var(ident), Var(Symbol("b"))))

                  def normalization(side0: Term, side1: Term) =
                    Normalization(side0, side1, Symbol("∘"), None, Set(Symbol("a"), Symbol("b")), reversible = true)

                  List(
                    normalization(side0, side1a),
                    normalization(side0, side1b))
              }).flatten
            else
              List.empty

          val binaryDistributivityConjectures =
            if closedBinaryOperation then
              val tpe = Function(tpe0, Function(tpe0, tpe0))
              (expr1.syntacticInfo.freeVars.keySet.toList.sorted collect {
                case ident if env.get(ident) exists { _.termType exists { equivalent(tpe, _) } } =>
                  val identProperties = env(ident).info(Abstraction) flatMap abstractionProperties.get getOrElse Set.empty

                  def side0(properties0: Properties, ident0: Symbol, properties1: Properties, ident1: Symbol) = App(Set.empty,
                    App(properties0, Var(ident0), Var(Symbol("a"))),
                    App(Set.empty, App(properties1, Var(ident1), Var(Symbol("b"))), Var(Symbol("c"))))

                  def side1(properties0: Properties, ident0: Symbol, properties1: Properties, ident1: Symbol) = App(Set.empty,
                    App(properties1, Var(ident1), App(Set.empty, App(properties0, Var(ident0), Var(Symbol("a"))), Var(Symbol("b")))),
                    App(Set.empty, App(properties0, Var(ident0), Var(Symbol("a"))), Var(Symbol("c"))))

                  def normalization(side0: Term, side1: Term) =
                    Normalization(side0, side1, Symbol("∘"), None, Set(Symbol("a"), Symbol("b"), Symbol("c")), reversible = true)

                  List(
                    normalization(
                      side0(properties, Symbol("∘"), identProperties, ident),
                      side1(properties, Symbol("∘"), identProperties, ident)),
                    normalization(
                      side0(identProperties, ident, properties, Symbol("∘")),
                      side1(identProperties, ident, properties, Symbol("∘"))))
              }).flatten
            else
              List.empty

          val generalizedConjectures =
            if closedBinaryOperation then
              Conjecture.generalizedConjectures(properties, term, ident0, ident1, tpe0, result)
            else
              List.empty

          unaryDistributivityConjectures ++
          binaryDistributivityConjectures ++
          generalizedConjectures filterNot {
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

      val assumedNormalizeConjecture =
        if call.nonEmpty then assumedConjectures map { conjecture =>
            conjecture.checking(
                  call.get,
                  _ forall { _.info(Abstraction) contains abstraction.get },
                  _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                    val abstraction = expr.info(Abstraction)
                    abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
                  } },
                  (conjecture.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap).normalize
        } else List.empty

      def proveConjectures(
          conjectures: List[Normalization],
          provenConjectures: List[Normalization] = assumedConjectures,
          normalizeConjectures: List[Equalities => PartialFunction[Term, Term]] = assumedNormalizeConjecture)
      : (List[Normalization], List[Equalities => PartialFunction[Term, Term]]) =

        val init = (List.empty[Normalization], List.empty[(Normalization, Equalities => PartialFunction[Term, Term])])

        val (remaining, additional) = conjectures.foldLeft(init) { case (processed @ (remaining, proven), conjecture) =>
          if !Normalization.specializationForSameAbstraction(conjecture, proven map { case proven -> _ => proven }) then
            val checking = conjecture.checking(
              call.get,
              _ forall { _.info(Abstraction) contains abstraction.get },
              _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                val abstraction = expr.info(Abstraction)
                abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
              } },
              (conjecture.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap)

            val normalizeConjecture = checking.normalize

            val reverseChecking = conjecture.reverse map {
              _.checking(
                call.get,
                _ forall { _.info(Abstraction) contains abstraction.get },
                _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                  val abstraction = expr.info(Abstraction)
                  abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
                } },
                (conjecture.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap)
            }

            val reverseNormalizeConjecture = reverseChecking.toList map { _.normalize }

            def checkConjecture(checking: PropertyChecking.Normal) =
              val (expr, equalities) = checking.prepare(ident0, ident1, expr1)
              val converted = UniqueNames.convert(expr, names)

              if printReductionDebugInfo then
                println()
                println(indent(2, s"Checking conjecture: ${conjecture.show}"))
                println()
                println(indent(4, converted.wrapped.show))

              val config = Symbolic.Configuration(
                evaluator.properties.normalize(
                  normalizeFacts ++ (
                  normalizeConjecture ::
                  reverseNormalizeConjecture ++
                  normalizeConjectures ++
                  collectedNormalize ++
                  normalizing), _, _),
                evaluator.properties.derive(
                  derivingCompound,
                  deriveTypeContradiction :: derivingSimple, _),
                checking.control)

              val result = Symbolic.eval(converted, equalities, config)

              val check = checking.check(result.wrapped)
              val proved = check exists { _.reductions.isEmpty }
              val disproved = check.isLeft

              if printReductionDebugInfo then
                println()
                println(indent(2, "Evaluation result for conjecture check:"))
                if !proved then
                  println(indent(2, "(some cases may not be fully reduced)"))
                println()
                println(indent(4, result.wrapped.show))
                if !proved then
                  println()
                  println(indent(2, "Offending cases for conjecture check:"))
                  println(indent(2, "(some cases may not be fully reduced)"))
                  println()
                  println(indent(4, check.merge.show))
                println()
                if proved then
                  println(indent(4, "✔ Conjecture proven".toUpperCase.nn))
                else if disproved then
                  println(indent(4, "  Conjecture disproved".toUpperCase.nn))
                else
                  println(indent(4, "✘ Conjecture could not be proved".toUpperCase.nn))

              (proved, disproved)
            end checkConjecture

            val (proved, disproved) =
              val result @ (proved, disproved) = checkConjecture(checking)
              if !proved && !disproved && reverseChecking.isDefined then checkConjecture(reverseChecking.get)
              else result

            if proved then
              conjecture.reverse match
                case Some(reverseConjecture) =>
                  (remaining, (conjecture -> normalizeConjecture) :: (reverseConjecture -> reverseNormalizeConjecture.head) :: proven)
                case _ =>
                  (remaining, (conjecture -> normalizeConjecture) :: proven)
            else if disproved then
              (remaining, proven)
            else
              (conjecture :: remaining, proven)
          else
            processed
        }

        val (proven, normalize) = additional.unzip

        if remaining.isEmpty || additional.isEmpty then
          (provenConjectures ++ proven, normalizeConjectures ++ normalize)
        else
          proveConjectures(remaining, provenConjectures ++ proven, normalizeConjectures ++ normalize)
      end proveConjectures

      val (provenConjectures, normalizeConjectures) = proveConjectures(conjectures sortWith {
        !Normalization.specializationForSameAbstraction(_, _)
      })

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
          sortBy { case Normalization(pattern, result, _, _, _, _) -> _ =>
            (pattern, result)
          }).unzip

      addCollectedNormalizations(env, abstraction, provenProperties)

      if printDeductionDebugInfo && conjectures.nonEmpty && provenProperties.nonEmpty then
        println()
        println(indent(2, "Proven properties:"))
        println()
        provenProperties foreach { property => println(indent(4, property.show)) }

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
                evaluator.properties.derive(derivingCompound, deriveTypeContradiction :: derivingSimple, _),
                checking.control)

              val result = Symbolic.eval(converted, equalities, config)

              val check = checking.check(result.wrapped)
              val proved = check exists { _.reductions.isEmpty }
              val disproved = check.isLeft

              if printReductionDebugInfo then
                println()
                println(indent(2, s"Evaluation result for ${property.show} property check:"))
                if !proved then
                  println(indent(2, "(some cases may not be fully reduced)"))
                println()
                println(indent(4, result.wrapped.show))
                if !proved then
                  println()
                  println(indent(2, s"Offending cases for ${property.show} property check:"))
                  println(indent(2, "(some cases may not be fully reduced)"))
                  println()
                  println(indent(4, check.merge.show))

              if printReductionDebugInfo || printDeductionDebugInfo then
                println()
                if proved then
                  println(indent(4, s"✔ ${property.show} property proven".toUpperCase.nn))
                else if disproved then
                  println(indent(4, s"✘ ${property.show} property disproved".toUpperCase.nn))
                else
                  println(indent(4, s"✘ ${property.show} property could not be proved".toUpperCase.nn))

              if disproved then Some(propertyDisprovenError(property))
              else if !proved then Some(propertyDeductionError(property))
              else None
      }
      error match
        case Some(error) => term.withExtrinsicInfo(error)
        case _ => Abs(term)(properties, ident0, tpe0, check(expr0, env + (ident0 -> typedArgVar(ident0, term.termType))))

    case Abs(properties, ident, tpe, expr) =>
      if properties.nonEmpty then
        term.withExtrinsicInfo(illshapedDefinitionError(properties.head))
      else
        if printReductionDebugInfo || printDeductionDebugInfo then
          if debugInfoPrinted then
            println()
          else
            debugInfoPrinted = true
          println("Checking properties for definition:")
          println()
          println(indent(2, term.show))

        val names = env.keys map { _.name }

        val abstraction = term.info(Abstraction)

        val facts = exprArgumentPrefixes(term) flatMap { (idents, expr) =>
          Conjecture.basicFacts(properties, term, idents, Symbolic.eval(UniqueNames.convert(expr, names)))
        }

        if printDeductionDebugInfo && facts.nonEmpty then
          println()
          println(indent(2, "Basic facts:"))
          println()
          facts map { fact => println(indent(4, fact.show)) }

        addCollectedNormalizations(env, abstraction, facts)

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
