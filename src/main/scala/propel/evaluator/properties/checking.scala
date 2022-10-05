package propel
package evaluator
package properties

import ast.*
import printing.*
import typer.*
import util.*

def check(
    expr: Term,
    assumedUncheckedConjectures: List[Normalization] = List.empty,
    printDeductionDebugInfo: Boolean = false,
    printReductionDebugInfo: Boolean = false): Term =
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

  val (abstractionProperties, abstractionResultTypes, abstractionNames) =
    def abstractionInfos(term: Term)
      : (Map[Abstraction, Properties], Map[Abstraction, Type], Map[Abstraction, String]) =
      term match
        case Abs(properties, _, _, expr) =>
          term.info(Abstraction) flatMap { abstraction =>
            expr.termType map { tpe =>
              val (exprProperties, exprResultTypes, exprNames) = abstractionInfos(expr)
              (exprProperties + (abstraction -> properties), exprResultTypes + (abstraction -> tpe), exprNames)
            }
          } getOrElse abstractionInfos(expr)
        case App(_, expr, arg) =>
          val (exprProperties, exprResultTypes, exprNames) = abstractionInfos(expr)
          val (argProperties, argResultTypes, argNames) = abstractionInfos(arg)
          (exprProperties ++ argProperties, exprResultTypes ++ argResultTypes, exprNames ++ argNames)
        case TypeAbs(_, expr) =>
          abstractionInfos(expr)
        case TypeApp(expr, _) =>
          abstractionInfos(expr)
        case Data(_, args) =>
          val (argsProperties, argsResultTypes, argsNames) = (args map abstractionInfos).unzip3
          (argsProperties.flatten.toMap, argsResultTypes.flatten.toMap, argsNames.flatten.toMap)
        case Var(ident) =>
          (Map.empty, Map.empty, (term.info(Abstraction) map { _ -> ident.name }).toMap)
        case Cases(scrutinee, cases) =>
          val (scrutineeProperties, scrutineeResultTypes, scrutineeNames) = abstractionInfos(scrutinee)
          val (casesProperties, casesResultTypes, casesNames) = (cases map { (_, expr) => abstractionInfos(expr) }).unzip3
          (scrutineeProperties ++ casesProperties.flatten.toMap,
           scrutineeResultTypes ++ casesResultTypes.flatten.toMap,
           scrutineeNames ++ casesNames.flatten.toMap)

    abstractionInfos(typedExpr)

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
      val abstractions =
        def abstractions(expr: Term): Map[Abstraction, Term] = expr.termType match
          case Some(Function(Sum(List(ctor -> List())), _)) =>
            val abstraction = expr.info(Abstraction)
            val properties = abstraction flatMap abstractionProperties.get getOrElse Set.empty
            val result = App(properties, expr, Data(ctor, List.empty)).typedTerm
            abstractions(result) ++ (abstraction map { _ -> result })
          case Some(Sum(List(ctor -> args))) =>
            val size = args.size
            (args.zipWithIndex flatMap { (arg, index) =>
              val name = arg.info(Abstraction) map { abstractionNames.get(_) getOrElse "∘" } getOrElse "∙"
              val args = List.tabulate(size) { i => Bind(Symbol(if i == index then name else "_")) }
              val result = Cases(expr, List(Match(ctor, args) -> Var(Symbol(name)))).typedTerm
              abstractions(result)
            }).toMap
          case _ =>
           (expr.info(Abstraction) map { _ -> expr }).toMap

        env flatMap { (_, expr) => abstractions(expr) }

      val (abstraction, call) = (term.info(Abstraction), recursiveCalls(term)) match
        case (abstraction @ Some(_), call :: _) => (abstraction, Some(call))
        case _ => (None, None)

      val names = env.keys map { _.name }

      val name = term.info(Abstraction) flatMap abstractionNames.get

      val collectedNormalize = collectedNormalizations flatMap { _(abstractions.get) }

      if printReductionDebugInfo || printDeductionDebugInfo then
        if debugInfoPrinted then
          println()
        else
          debugInfoPrinted = true
        println(s"Checking properties for definition${ name map { name => s" ($name)" } getOrElse "" }:")
        println()
        println(indent(2, term.show))

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
          Conjecture.distributivityConjectures(properties, term) ++
          Conjecture.generalizedConjectures(properties, term, ident0, ident1, tpe0, result) filterNot {
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

      val (uncheckedConjectures, uncheckedNormalizeConjecture) =
        if call.nonEmpty then
          (assumedUncheckedConjectures collect { case conjecture if name contains conjecture.abstraction.name =>
            conjecture -> conjecture.checking(
              call.get,
              _ forall { _.info(Abstraction) contains abstraction.get },
              _ forall { (ident, exprs) => env.get(ident) exists { expr =>
                val abstraction = expr.info(Abstraction)
                abstraction exists { abstraction => exprs forall { _.info(Abstraction) contains abstraction } }
              } },
              (conjecture.free flatMap { ident => env.get(ident) map { ident -> _ } }).toMap).normalize
          }).unzip
        else
          List.empty -> List.empty

      val (provenConjectures, normalizeConjectures) = proveConjectures(
        conjectures sortWith { !Normalization.specializationForSameAbstraction(_, _) },
        uncheckedConjectures,
        uncheckedNormalizeConjecture)

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

      if printDeductionDebugInfo && (conjectures.nonEmpty || uncheckedConjectures.nonEmpty) && provenProperties.nonEmpty then
        println()
        println(indent(2, "Proven properties:"))
        println()
        provenProperties foreach { property => println(indent(4, property.show)) }

      val resultType = term.termType collect { case Function(_, Function(_, result)) => result }

      val error = properties collectFirstDefined { property =>
        propertiesChecking get property match
          case None =>
            Some(unknownPropertyError(property))
          case Some(checking) =>
            if checking.propertyType == PropertyType.Relation &&
               (!equivalent(tpe0, tpe1) || (resultType forall { !equivalent(boolType, _) })) then
              Some(illformedRelationTypeError(property, term.termType))
            else if checking.propertyType == PropertyType.Function &&
               (!equivalent(tpe0, tpe1) || (resultType forall { !equivalent(tpe0, _) })) then
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
        val abstraction = term.info(Abstraction)

        val names = env.keys map { _.name }

        val name = abstraction flatMap abstractionNames.get

        if printReductionDebugInfo || printDeductionDebugInfo then
          if debugInfoPrinted then
            println()
          else
            debugInfoPrinted = true
          println(s"Checking properties for definition${ name map { name => s" ($name)" } getOrElse "" }:")
          println()
          println(indent(2, term.show))

        val facts = exprArgumentPrefixes(term) flatMap { (idents, expr) =>
          Conjecture.basicFacts(properties, term, idents, Symbolic.eval(UniqueNames.convert(expr, names)))
        }

        if printDeductionDebugInfo && facts.nonEmpty then
          println()
          println(indent(2, "Basic facts:"))
          println()
          facts map { fact => println(indent(4, fact.show)) }

        val uncheckedConjectures = assumedUncheckedConjectures collect { case conjecture if name contains conjecture.abstraction.name =>
          conjecture
        }

        if printDeductionDebugInfo && uncheckedConjectures.nonEmpty then
          println()
          println(indent(2, "Generalized conjectures:"))
          println()
          uncheckedConjectures map { conjecture => println(indent(4, conjecture.show)) }
          println()
          println(indent(2, "Proven properties:"))
          println()
          uncheckedConjectures foreach { property => println(indent(4, property.show)) }

        addCollectedNormalizations(env, abstraction, facts ++ uncheckedConjectures)

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
