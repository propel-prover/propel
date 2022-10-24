package propel
package evaluator
package properties

import ast.*
import typer.*
import util.*

object Conjecture:
  private def containsReference(expr: Term, abstraction: Abstraction): Boolean =
    (expr.info(Abstraction) contains abstraction) || {
      expr match
        case Abs(_, _, _, expr) => containsReference(expr, abstraction)
        case App(_, expr, arg) => containsReference(expr, abstraction) || containsReference(arg, abstraction)
        case TypeAbs(ident, expr) => containsReference(expr, abstraction)
        case TypeApp(expr, tpe) => containsReference(expr, abstraction)
        case Data(_, args) => args exists { containsReference(_, abstraction) }
        case Var(_) => false
        case Cases(scrutinee, cases) => containsReference(scrutinee, abstraction) || (cases exists { (_, expr) =>
          containsReference(expr, abstraction)
        })
    }

  private def replaceAbstraction(term: Term, from: Abstraction, to: Term): Term =
    if term.info(Abstraction) contains from then
      to
    else
      term match
        case Abs(properties, ident, tpe, expr) =>
          Abs(term)(properties, ident, tpe, replaceAbstraction(expr, from, to))
        case App(properties, expr, arg) =>
          App(term)(properties, replaceAbstraction(expr, from, to), replaceAbstraction(arg, from, to))
        case TypeAbs(ident, expr) =>
          TypeAbs(term)(ident, replaceAbstraction(expr, from, to))
        case TypeApp(expr, tpe) =>
          TypeApp(term)(replaceAbstraction(expr, from, to), tpe)
        case Data(ctor, args) =>
          Data(term)(ctor, args map { replaceAbstraction(_, from, to) })
        case Var(_) =>
          term
        case Cases(scrutinee, cases) =>
          Cases(term)(replaceAbstraction(scrutinee, from, to), cases map { _ -> replaceAbstraction(_, from, to) })

  private def normalizable(normalize: PartialFunction[Term, ?], expr: Term): Boolean =
    (normalize isDefinedAt expr) || {
    expr match
      case Abs(_, _, _, expr) => normalizable(normalize, expr)
      case App(_, expr, arg) => normalizable(normalize, expr) || normalizable(normalize, arg)
      case TypeAbs(ident, expr) => normalizable(normalize, expr)
      case TypeApp(expr, tpe) => normalizable(normalize, expr)
      case Data(_, args) => args exists { normalizable(normalize, _) }
      case Var(_) => false
      case Cases(scrutinee, cases) => normalizable(normalize, scrutinee) || (cases exists { (_, expr) =>
        normalizable(normalize, expr)
      })
    }

  private def recursiveNormalization(
      lhs: Term,
      rhs: Term,
      abstraction: Abstraction,
      call: Option[Term],
      unbound: Set[Symbol],
      names: Set[String]) =
    val ident = Naming.freshIdent(Symbol("∘"), names)
    val variable = Var(ident)
    let(replaceAbstraction(lhs, abstraction, variable)) { lhs =>
      let(replaceAbstraction(rhs, abstraction, variable)) { rhs =>
        createNormalization(lhs, rhs, ident, abstraction, call, unbound, Symbolic.Constraints.empty, names)
      }
    }

  private def directNormalization(
      properties: Abstraction => Option[Properties],
      tpe: Option[Type],
      args: List[Term],
      rhs: Term,
      abstraction: Abstraction,
      unbound: Set[Symbol],
      constraints: Symbolic.Constraints,
      names: Set[String]) =
    val ident = Naming.freshIdent(Symbol("∘"), names)
    val lhs = app(properties, Var(ident), args, tpe)
    createNormalization(lhs, rhs, ident, abstraction, None, unbound, constraints, names)

  private def createNormalization(
      lhs: Term,
      rhs: Term,
      ident: Symbol,
      abstraction: Abstraction,
      call: Option[Term],
      unbound: Set[Symbol],
      constraints: Symbolic.Constraints,
      names: Set[String]) =
    let(rhs.syntactic) { (rhs, rhsInfo) =>
      let(lhs.syntactic) { (lhs, lhsInfo) =>
        val constrained = constraints.pos.keys flatMap { _.syntacticInfo.freeVars.keys }
        val remaining = rhsInfo.freeVars.keySet -- lhsInfo.freeVars.keySet - ident

        if !(constrained exists { unbound contains _ }) && (remaining forall { unbound contains _ }) then
          def dummy = Data(Constructor(Symbol("∅")), List.empty)
          val variables = rhsInfo.freeVars.keySet ++ lhsInfo.freeVars.keySet -- unbound - ident
          val normalization = Normalization(lhs, rhs, ident, variables, reversible = false)
          val checking = normalization.checking(
            call getOrElse dummy,
            _ forall { _.info(Abstraction) contains abstraction },
            _ forall { (ident, exprs) => exprs forall {
              case expr @ Var(_) => expr.ident == ident
              case _ => false
            } },
            (normalization.free map { ident => ident -> Var(ident) }).toMap)
          val normalize = checking.normalize(Equalities.empty)
          lhs -> Option.when(!normalizable(normalize, normalization.checking.result))(normalization)
        else
          lhs -> None
      }
    }
  end createNormalization

  private object app:
    def apply(properties: Abstraction => Option[Properties], expr: Term, args: List[Term], tpe: Option[Type] = None) =
      def makeApp(expr: Term, arg: Term, tpe: Option[Type]) =
        val info = tpe collect { case tpe @ Function(_, result) => (tpe.info(Abstraction), result.info(Abstraction), result) }
        val tpeAbstraction = info flatMap { (abstraction, _, _) => abstraction }
        val resultAbstraction = info flatMap { (_, abstraction, _) => abstraction }
        val result = info map { (_, _, result) => result }
        val term = App(tpeAbstraction flatMap properties getOrElse Set.empty, expr, arg)

        resultAbstraction match
          case Some(abstraction) => term.withExtrinsicInfo(abstraction) -> result
          case _ => term -> result

      if args.isEmpty then
        expr
      else
        val (result, _) = args.tail.foldLeft(makeApp(expr, args.head, tpe)) { case ((expr, tpe), arg) => makeApp(expr, arg, tpe) }
        result

    def unapply(expr: Term): Option[(Term, List[Term])] = expr match
      case App(_, expr, arg) => unapply(expr) match
        case Some(expr, args) => Some(expr, args :+ arg)
        case _ => Some(expr, List(arg))
      case _ =>
        None

  def basicFacts(
      properties: Abstraction => Option[Properties],
      isAbstraction: Symbol => Boolean,
      abstraction: Term,
      recursiveCall: Option[Term],
      idents: List[Symbol],
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    val unbound = abstraction.syntacticInfo.freeVars.keySet
    val tpe = abstraction.termType

    abstraction.info(Abstraction) match
      case Some(abstraction) =>
        result unwrap { result =>
          val names = UniqueNames.usedNames.toSet

          val (_, normalizations) = result.reductions.foldLeft(List.empty[Term], List.empty[Normalization]) {
            case ((patterns, normalizations), Symbolic.Reduction(expr, constraints, equalities)) =>
              let(expr.syntactic) { (expr, exprInfo) =>
                val freeVars = exprInfo.freeVars.keySet

                val variableArgs = idents map { ident =>
                  val variable = Var(ident)
                  variable -> (Option.when(freeVars contains ident)(variable) orElse equalities.pos.get(variable) getOrElse variable)
                }

                val (vars, args) = variableArgs.unzip

                val lhs -> normalization = recursiveCall match
                  case Some(call) =>
                    recursiveNormalization(app(properties, call, args, tpe), expr, abstraction, recursiveCall, unbound, names)
                  case _ =>
                    directNormalization(properties, tpe, args, expr, abstraction, unbound, constraints, names)

                (lhs :: patterns) -> (normalization match {
                  case Some(normalization)
                      if (patterns forall { Unification.refutable(normalization.checking.pattern, _) }) &&
                         (variableArgs exists { _ != _ }) &&
                         (normalization.free forall isAbstraction) =>
                    normalization :: normalizations
                  case _ =>
                    normalizations
                })
              }
          }

          Normalization.distinct(normalizations) sortBy {
            case Normalization(pattern, result, _, _, _) => (pattern, result)
          }
        }
      case _ =>
        List.empty
  end basicFacts

  def auxiliaryArgumentsConjectures(
      properties: Abstraction => Option[Properties],
      abstraction: Term,
      idents: List[Symbol],
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    enum Struct:
      def dependent: Boolean
      def independent: Boolean
      case Node(ctor: Constructor, args: List[Struct], dependent: Boolean, independent: Boolean)
      case Leaf(dependent: Boolean, independent: Boolean)

    (abstraction.termType, abstraction.info(Abstraction), recursiveCalls(abstraction)) match
      case (tpe, Some(abstraction), call :: _) =>
        idents.zipWithIndex flatMap { (ident, index) =>
          result unwrap { result =>
            val argumentAndStructs = result.reductions.foldLeft[Option[(Option[Term], Option[Struct])]](Some(None, None)) {
              case (None, _) =>
                None
              case (argumentAndStucts @ Some(argument, struct), Symbolic.Reduction(expr, _, equalities)) =>
                def createStruct(expr: Term): Struct = expr match
                  case Data(ctor, List()) =>
                    Struct.Node(ctor, List(), dependent = false, independent = true)
                  case Data(ctor, args) =>
                    let(args map createStruct) { args =>
                      Struct.Node(ctor, args, args forall { _.dependent }, args forall { _.independent })
                    }
                  case _ =>
                    val dependents = (equalities.pos.get(Var(ident)).toSet flatMap { _.syntacticInfo.freeVars.keys }) + ident
                    val dependent = expr.syntacticInfo.freeVars.keys exists { dependents contains _ }
                    Struct.Leaf(dependent, !dependent)

                def unifyStructs(struct0: Struct, struct1: Struct): Option[Struct] = struct0 -> struct1 match
                  case Struct.Node(ctor0, args0, dependent0, independent0) ->
                       Struct.Node(ctor1, args1, dependent1, independent1) if ctor0 == ctor1 =>
                    args0 zip args1 mapIfDefined unifyStructs map { args =>
                      Struct.Node(ctor0, args, args forall { _.dependent }, args forall { _.independent })
                    }
                  case _ =>
                    Option.when((struct0.dependent && struct1.dependent) != (struct0.independent && struct1.independent)) {
                      Struct.Leaf(struct0.dependent && struct1.dependent, struct0.independent && struct1.independent)
                    }

                if equalities.pos forall { !containsReference(_, abstraction) && !containsReference(_, abstraction) } then
                  expr match
                    case app(expr, args)
                      if (expr.info(Abstraction) contains abstraction) &&
                         (args forall { !containsReference(_, abstraction) }) =>
                      args.drop(index).headOption flatMap { arg =>
                        argument match
                          case Some(argument) => if equivalent(argument, arg) then argumentAndStucts else None
                          case _ => Some(Some(arg) -> struct)
                      }
                    case _ if !containsReference(expr, abstraction) =>
                      struct match
                        case Some(struct) => unifyStructs(struct, createStruct(expr)) map { argument -> Some(_) }
                        case _ => Some(argument -> Some(createStruct(expr)))
                    case _ =>
                      None
                else
                  None
            }

            def hasDependent(struct: Struct): Boolean = struct match
              case Struct.Node(_, args, dependent, _) => dependent || (args exists hasDependent)
              case Struct.Leaf(dependent, _) => dependent

            (argumentAndStructs collect { case (Some(argument), Some(struct)) if hasDependent(struct) =>
              val argumentInfo = argument.syntacticInfo

              Option.when(argumentInfo.freeVars contains ident) {
                val initialNames = (argumentInfo.boundVars map { _.name }) ++ (argumentInfo.freeVars map { (ident, _) => ident.name })

                val (abstractionIdent :: argumentIdents, names) =
                  (Symbol("∘") :: idents).foldRight[(List[Symbol], Set[String])](List.empty -> initialNames) {
                    case (ident, (idents, names)) =>
                      val fresh = Naming.freshIdent(ident, names)
                      (fresh :: idents) -> (names + fresh.name)
                  }

                val abstractionExpr = Var(abstractionIdent)
                val abstractionArgs = argumentIdents map { Var(_) }

                val rhs = app(
                  properties,
                  abstractionExpr,
                  abstractionArgs.updated(index, subst(argument, Map(ident -> abstractionArgs(index)))),
                  tpe)

                struct match
                  case Struct.Leaf(_, _) =>
                    Normalization(
                      rhs,
                      subst(argument, Map(ident -> app(properties, abstractionExpr, abstractionArgs, tpe))),
                      abstractionIdent,
                      argumentIdents.toSet,
                      reversible = false)

                  case _ =>
                    def createStruct(struct: Struct, names: Set[String]): (Pattern, Term, Set[String]) = struct match
                      case Struct.Node(ctor, args, _, _) =>
                        val (patterns, exprs, updatedNames) =
                          args.foldLeft[(List[Pattern], List[Term], Set[String])](List.empty, List.empty, names) {
                            case ((patterns, exprs, names), arg) =>
                              let(createStruct(arg, names)) { (pattern, expr, updatedNames) =>
                                (patterns :+ pattern, exprs :+ expr, updatedNames)
                              }
                          }
                        (Match(ctor, patterns), Data(ctor, exprs), updatedNames)
                      case Struct.Leaf(dependent, _) =>
                        val fresh = Naming.freshIdent(Symbol("v"), names)
                        if dependent then
                          (Bind(fresh), subst(argument, Map(ident -> Var(fresh))), names + fresh.name)
                        else
                          (Bind(fresh), Var(fresh), names + fresh.name)

                    val (pattern, expr, _) = createStruct(struct, names)

                    Normalization(
                      rhs,
                      Cases(app(properties, abstractionExpr, abstractionArgs, tpe), List(pattern -> expr)),
                      abstractionIdent,
                      argumentIdents.toSet,
                      reversible = false)
              }
            }).flatten
          }
        }

      case _ =>
        List.empty
  end auxiliaryArgumentsConjectures

  def generalizedConjectures(
      properties: Abstraction => Option[Properties],
      isAbstraction: Symbol => Boolean,
      abstraction: Term,
      recursiveCall: Term,
      identTypes: List[(Symbol, Type)],
      result: UniqueNames[Symbolic.Result]): List[Normalization] =
    val unbound = abstraction.syntacticInfo.freeVars.keySet

    val tpe = abstraction.termType

    def injectRecursiveCallBasedOnType(
        term: Term,
        resultType: Type,
        vars: List[Term],
        index: Int): List[Term] =
      val result = term match
        case Abs(properties, ident, tpe, expr) =>
          injectRecursiveCallBasedOnType(expr, resultType, vars, index) collect { Abs(term)(properties, ident, tpe, _) }
        case App(properties, expr, arg) =>
          (injectRecursiveCallBasedOnType(expr, resultType, vars, index) collect { App(term)(properties, _, arg) }) ++
          (injectRecursiveCallBasedOnType(arg, resultType, vars, index) collect { App(term)(properties, expr, _)  })
        case TypeAbs(ident, expr) =>
          injectRecursiveCallBasedOnType(expr, resultType, vars, index) collect { TypeAbs(ident, _) }
        case TypeApp(expr, tpe) =>
          injectRecursiveCallBasedOnType(expr, resultType, vars, index) collect { TypeApp(_, tpe) }
        case Data(ctor, args) =>
          def process(args: List[Term]): List[List[Term]] = args match
            case arg :: args =>
              (injectRecursiveCallBasedOnType(arg, resultType, vars, index) collect { _ :: args }) ++
              (process(args) map { arg :: _ })
            case _ =>
              List.empty
          process(args) map { Data(term)(ctor, _) }
        case Var(_) =>
          List.empty
        case Cases(scrutinee, cases) =>
          def process(cases: List[(Pattern, Term)]): List[List[(Pattern, Term)]] = cases match
            case (patternExpr @ (pattern -> expr)) :: cases =>
              (injectRecursiveCallBasedOnType(expr, resultType, vars, index) collect { pattern -> _ :: cases }) ++
              (process(cases) map { patternExpr :: _ })
            case _ =>
              List.empty
          (injectRecursiveCallBasedOnType(scrutinee, resultType, vars, index) collect { Cases(term)(_, cases) }) ++
          (process(cases) map { Cases(term)(scrutinee, _) })

      if term.termType exists { conforms(resultType, _) } then
        app(properties, recursiveCall, vars.updated(index, term), tpe) :: result
      else
        result
    end injectRecursiveCallBasedOnType

    def generalizeEvaluationResults(baseAbstraction: Abstraction, resultType: Type) =
      result unlinked { result =>
        val names = UniqueNames.usedNames.toSet

        val varNames = identTypes.foldRight(List.empty[String]) { case ((ident, _), varNames) =>
          def uniqueName(name: String): String =
            if name != ident.name && ((names.iterator ++ varNames.iterator) exists { _ == name }) then
              uniqueName(s"$name′")
            else
              name
          uniqueName(Naming.dropSubscript(ident.name)) :: varNames
        }

        val vars = varNames map { name => Var(Symbol(name)) }

        val patterns = varNames zip identTypes map { case (name, (_, tpe)) =>
          normalize(tpe) map { patternsByType(_, name, names) map { Var(Symbol(name)) -> _.withSyntacticInfo } } getOrElse List.empty
        }

        val patternsCombinations = patterns.foldRight(List(List.empty[(Term, Pattern)])) { (patterns, patternsCombinations) =>
          patternsCombinations flatMap { patternsCombinations => patterns map { _ :: patternsCombinations } }
        }

        patternsCombinations flatMap { patterns =>
          let(names ++ (patterns flatMap { (_, pattern) => pattern.syntacticInfo.boundVars map { _.name } })) { names =>
            PatternConstraints.make(patterns).toList flatMap { constraints =>
              result.withConstraints(constraints).reductions flatMap { case Symbolic.Reduction(expr, _, equalities) =>
                val args = patterns map { (variable, _) => equalities.pos.getOrElse(variable, variable) }

                val lhs = app(properties, recursiveCall, args, tpe)
                val (rhs, rhsInfo) = expr.syntactic

                val generalizations =
                  if !containsReference(rhs, baseAbstraction) then
                    val freeVars = rhsInfo.freeVars.keys

                    val varsDependents = vars map { variable =>
                      (equalities.pos.get(variable).toSet flatMap { _.syntacticInfo.freeVars.keys }) + variable.ident
                    }

                    val exprsDependOnVar = varsDependents map { varDependents =>
                      freeVars exists { varDependents contains _ }
                    }

                    exprsDependOnVar.zipWithIndex collect { case (true, index) => index } match
                      case List(index) if args(index).termType exists { conforms(_, resultType) } =>
                        val lhs = app(properties, recursiveCall, vars.updated(index, args(index)), tpe)
                        injectRecursiveCallBasedOnType(rhs.typedTerm, resultType, vars, index) collect {
                          case rhs if equalities.equal(rhs, lhs) != Equality.Equal => lhs -> rhs
                        }
                      case _ =>
                        List.empty
                  else
                    List.empty
                end generalizations

                lhs -> rhs :: generalizations flatMap { (lhs, rhs) =>
                  val _ -> normalization = recursiveNormalization(lhs, rhs, baseAbstraction, Some(recursiveCall), unbound, names)
                  normalization filter { _.free forall isAbstraction }
                }
              }
            }
          }
        }
      }

    def resultType(tpe: Type, idents: List[?]): Option[Type] = tpe match
      case Function(_, result) if idents.nonEmpty => resultType(result, idents.tail)
      case _ => Option.when(idents.isEmpty) { tpe }

    (abstraction.info(Abstraction), tpe.flatMap { resultType(_, identTypes) }) match
      case (Some(abstraction), Some(resultType)) =>
        generalizeEvaluationResults(abstraction, resultType) unwrap {
          Normalization.distinct(_) sortBy { case Normalization(pattern, result, _, _, _) => (pattern, result) }
        }
      case _ =>
        List.empty
  end generalizedConjectures

  def distributivityConjectures(properties: Properties, abstraction: Term): List[Normalization] =
    def freeVars(expr: Term) =
      val abstraction = expr.info(Abstraction)

      def freeVars(expr: Term, bound: Set[Symbol]): Map[Term, Properties] = expr match
        case Abs(_, ident, _, expr) => freeVars(expr, bound + ident)
        case App(properties, expr @ Var(ident), arg)
            if !(bound contains ident) && !(expr.info(Abstraction) exists { abstraction contains _ }) =>
          freeVars(arg, bound) + (expr -> properties)
        case App(_, expr, arg) => freeVars(expr, bound) ++ freeVars(arg, bound)
        case TypeAbs(_, expr) => freeVars(expr, bound)
        case TypeApp(expr, _) => freeVars(expr, bound)
        case Data(_, args) => (args flatMap { freeVars(_, bound) }).toMap
        case Var(_) => Map.empty
        case Cases(scrutinee, cases) => freeVars(scrutinee, bound) ++ (cases flatMap { (_, expr) => freeVars(expr, bound) })

      freeVars(expr, Set.empty)
    end freeVars

    def binaryBinaryConjectures(binary0: Term, binary0Properties: Properties, binary1: Term, binary1Properties: Properties) =
      def side0(properties0: Properties, expr0: Term, properties1: Properties, expr1: Term) = App(Set.empty,
        App(properties0, expr0, Var(Symbol("a"))),
        App(Set.empty, App(properties1, expr1, Var(Symbol("b"))), Var(Symbol("c"))))

      def side1(properties0: Properties, expr0: Term, properties1: Properties, expr1: Term) = App(Set.empty,
        App(properties1, expr1, App(Set.empty, App(properties0, expr0, Var(Symbol("a"))), Var(Symbol("b")))),
        App(Set.empty, App(properties0, expr0, Var(Symbol("a"))), Var(Symbol("c"))))

      def normalization(side0: Term, side1: Term) =
        Normalization(side0, side1, Symbol("∘"), Set(Symbol("a"), Symbol("b"), Symbol("c")), reversible = true)

      List(
        normalization(
          side0(binary0Properties, binary0, binary1Properties, binary1),
          side1(binary0Properties, binary0, binary1Properties, binary1)),
        normalization(
          side0(binary1Properties, binary1, binary0Properties, binary0),
          side1(binary1Properties, binary1, binary0Properties, binary0)))

    def unaryBinaryConjectures(unary: Term, unaryProperties: Properties, binary: Term, binaryProperties: Properties) =
      val side0 = App(unaryProperties, unary,
        App(Set.empty, App(binaryProperties, binary, Var(Symbol("a"))), Var(Symbol("b"))))

      val side1a = App(Set.empty,
        App(binaryProperties, binary, App(unaryProperties, unary, Var(Symbol("a")))), Var(Symbol("b")))

      val side1b = App(Set.empty,
        App(binaryProperties, binary, Var(Symbol("a"))), App(unaryProperties, unary, Var(Symbol("b"))))

      def normalization(side0: Term, side1: Term) =
        Normalization(side0, side1, Symbol("∘"), Set(Symbol("a"), Symbol("b")), reversible = true)

      List(
        normalization(side0, side1a),
        normalization(side0, side1b))

    def unaryUnaryConjectures(unary0: Term, unary0Properties: Properties, unary1: Term, unary1Properties: Properties) =
      def side(properties0: Properties, expr0: Term, properties1: Properties, expr1: Term) =
        App(properties0, expr0, App(properties1, expr1, Var(Symbol("a"))))

      def normalization(side0: Term, side1: Term) =
        Normalization(side0, side1, Symbol("∘"), Set(Symbol("a")), reversible = true)

      List(
        normalization(
          side(unary0Properties, unary0, unary1Properties, unary1),
          side(unary1Properties, unary1, unary0Properties, unary0)))

    abstraction.termType match
      case Some(Function(tpe0, Function(tpe1, tpe2))) if equivalent(tpe0, tpe1) && equivalent(tpe1, tpe2) =>
        val unaryType = Function(tpe0, tpe0)
        val binaryType = Function(tpe0, Function(tpe0, tpe0))

        freeVars(abstraction).toList sortBy { (expr, _) => expr } flatMap { (expr, exprProperties) =>
          expr.termType.toList flatMap { tpe =>
            if equivalent(tpe, unaryType) then unaryBinaryConjectures(expr, exprProperties, Var(Symbol("∘")), properties)
            else if equivalent(tpe, binaryType) then binaryBinaryConjectures(expr, exprProperties, Var(Symbol("∘")), properties)
            else List.empty
          }
        }

      case Some(Function(tpe0, tpe1)) if equivalent(tpe0, tpe1) =>
        val unaryType = Function(tpe0, tpe0)
        val binaryType = Function(tpe0, Function(tpe0, tpe0))

        freeVars(abstraction).toList sortBy { (expr, _) => expr } flatMap { (expr, exprProperties) =>
          expr.termType.toList flatMap { tpe =>
            if equivalent(tpe, unaryType) then unaryUnaryConjectures(Var(Symbol("∘")), properties, expr, exprProperties)
            else if equivalent(tpe, binaryType) then binaryBinaryConjectures(Var(Symbol("∘")), properties, expr, exprProperties)
            else List.empty
          }
        }

      case _ =>
        List.empty
  end distributivityConjectures
end Conjecture
