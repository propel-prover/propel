package propel
package dsl.impl

import ast.{Type => _, Term => _, Property => _, dsl => _, *}
import typer.*

import dsl.scala.*

import scala.deriving.Mirror
import scala.quoted.*

object Checked:
  def check[T: Type](f: Expr[Any], recursive: Boolean)(using Quotes) =
    import quotes.reflect.*

    def reportErrors(expr: ast.Term) =
      val errors = expr.errors
      if errors.nonEmpty then
        report.errorAndAbort((errors map { case (_, Error(message)) => message }).mkString("", "\n\n", ""))

    val Typed(fTerm, _) = f.asTerm.underlyingArgument: @unchecked
    val (result, recursiveSymbol, expr, typeVars) = processPropDef[T](fTerm, Set.empty, recursive)

    recursiveSymbol match
      case Some(recursiveSymbol) =>
        val (tpe @ Function(t, u), _) = makeType(TypeRepr.of[T], Position.ofMacroExpansion): @unchecked
        val recursiveExpr = App(Set.empty,
          TypeApp(TypeApp(zCombinator, t), u),
          Abs(Set.empty, scala.Symbol(recursiveSymbol.name), tpe, expr))

        reportErrors(evaluator.properties.check(recursiveExpr))

        val Block(List(recursiveDefinition), _) = '{ var rec: T = null.asInstanceOf[T] }.asTerm.underlyingArgument: @unchecked
        val recursiveCall = Ref(recursiveDefinition.symbol)

        Typed(
          Block(
            List(
              recursiveDefinition,
              Assign(recursiveCall,
                replaceRecursiveCall(Map(recursiveSymbol -> recursiveCall), result, Symbol.spliceOwner))),
            recursiveCall),
          TypeTree.of[T]).asExprOf[T]

      case _ =>
        reportErrors(evaluator.properties.check(expr))
        Typed(result, TypeTree.of[T]).asExprOf[T]
  end check

  val zCombinator =
    import ast.dsl.*
    tpabs("T", "U")(abs("f" -> tp(("T" -> "U") -> ("T" -> "U")))(
      abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v")),
      abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v"))))

  def processPropExpr(using Quotes)(
      term: quotes.reflect.Term,
      bound: Set[quotes.reflect.Symbol]): (quotes.reflect.Term, ast.Term, Set[scala.Symbol]) =
    import quotes.reflect.*

    val propertyFunction = TypeRepr.of[Any := (Nothing, Nothing) =>: _]
    val boolean = TypeRepr.of[Boolean]
    val list = TypeRepr.of[List[_]]
    val cons = Constructor(scala.Symbol(productName(TypeRepr.of[::[_]])))

    def isStableOuterReference(term: Term): Boolean =
      val symbol = term.symbol
      val stable =
        !(bound contains term.symbol) &&
        symbol.isTerm &&
        ((!(symbol.flags is quotes.reflect.Flags.Mutable) &&
          !(symbol.flags is quotes.reflect.Flags.Method)) ||
         (symbol.flags is quotes.reflect.Flags.StableRealizable))
      term match
        case Ident(_) => stable
        case Select(qualifier, _) => stable && isStableOuterReference(qualifier)
        case _ => false

    def hasStableOuterReferencePath(term: Ref) = term match
      case Ident(_) => true
      case Select(qualifier, _) => isStableOuterReference(qualifier)

    def dataConstructor(term: Term) =
      def dataConstructor(tpe: TypeRepr) =
        if isProduct(tpe) then
          Some(Constructor(scala.Symbol(productName(tpe))))
        else if tpe.typeSymbol.companionClass.exists then
          val companion = TypeIdent(tpe.typeSymbol.companionClass).tpe
          Option.when(isProduct(companion)) { Constructor(scala.Symbol(productName(companion))) }
        else
          None

      term match
        case Literal(BooleanConstant(true)) => Some(Constructor.True)
        case Literal(BooleanConstant(false)) => Some(Constructor.False)
        case _ if isStableOuterReference(term) => dataConstructor(term.tpe.widenTermRefByName) orElse dataConstructor(term.tpe)
        case _ => None
    end dataConstructor

    term match
      case Typed(expr, tpt) =>
        val (exprTerm, exprExpr, exprTypeVars) = processPropExpr(expr, bound)
        (Typed(exprTerm, tpt), exprExpr, exprTypeVars)

      case Ident(name) if bound contains term.symbol =>
        (term, Var(scala.Symbol(name)), Set.empty)

      case term: Ref if hasStableOuterReferencePath(term) =>
        dataConstructor(term) match
          case Some(ctor) =>
            (term, Data(ctor, List.empty), Set.empty)
          case _ =>
            val (tpe, typeVars) = makeType(term.tpe.widenTermRefByName, term.pos)
            val expr = Var(scala.Symbol(term.symbol.fullName)).withExtrinsicInfo(Typing.Specified(Right(tpe)))
            (term, expr, typeVars)

      case Apply(select @ Select(qual, name @ ("==" | "!=")), List(arg))
          if (qual.tpe.widenTermRefByName <:< arg.tpe.widenTermRefByName ||
              arg.tpe.widenTermRefByName <:< qual.tpe.widenTermRefByName) &&
             isAlgebraic(qual.tpe.widenTermRefByName) &&
             isAlgebraic(arg.tpe.widenTermRefByName) =>
        val (qualTerm, qualExpr, qualTypeVars) = processPropExpr(qual, bound)
        val (argTerm, argExpr, argTypeVars) = processPropExpr(arg, bound)
        val (tpe, typeVars) =
          if qual.tpe.widenTermRefByName <:< arg.tpe.widenTermRefByName then
            makeType(arg.tpe.widenTermRefByName, select.pos)
          else
            makeType(qual.tpe.widenTermRefByName, select.pos)
        val term = qualTerm.select(select.symbol).appliedTo(argTerm)
        val booleanType = Sum(List(Constructor.True -> List.empty, Constructor.False -> List.empty))
        val relationType = Function(tpe, Function(tpe, booleanType))
        val relationExpr = App(Set.empty,
          App(Set(Reflexive, Symmetric, Antisymmetric, Transitive),
            Var(scala.Symbol("<synthetic algebraic equality>")).withExtrinsicInfo(Typing.Specified(Right(relationType))),
            qualExpr),
          argExpr)
        val expr = name match
          case "==" => relationExpr
          case "!=" => Cases(relationExpr, List(
            ast.Match(Constructor.True, List.empty) -> Data(Constructor.False, List.empty),
            ast.Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))
        (term, expr, qualTypeVars ++ argTypeVars ++ typeVars)

      case Apply(TypeApply(Select(qual, "::"), targs), List(arg)) if qual.tpe <:< list =>
        val (qualTerm, qualExpr, qualTypeVars) = processPropExpr(qual, bound)
        val (argTerm, argExpr, argTypeVars) = processPropExpr(arg, bound)
        val term = Select.unique(qualTerm, "::").appliedToTypeTrees(targs).appliedTo(argTerm)
        val expr = Data(cons, List(argExpr, qualExpr))
        (term, expr, qualTypeVars ++ argTypeVars)

      case Apply(Select(qual, name @ ("&&" | "||")), List(arg)) if qual.tpe <:< boolean =>
        val (qualTerm, qualExpr, qualTypeVars) = processPropExpr(qual, bound)
        val (argTerm, argExpr, argTypeVars) = processPropExpr(arg, bound)
        val term = Select.unique(qualTerm, name).appliedTo(argTerm)
        val expr = name match
          case "&&" => Cases(qualExpr, List(
            ast.Match(Constructor.True, List.empty) -> argExpr,
            ast.Match(Constructor.False, List.empty) -> Data(Constructor.False, List.empty)))
          case "||" => Cases(qualExpr, List(
            ast.Match(Constructor.True, List.empty) -> Data(Constructor.True, List.empty),
            ast.Match(Constructor.False, List.empty) -> argExpr))
        (term, expr, qualTypeVars ++ argTypeVars)

      case Select(qual, "unary_!") if qual.tpe <:< boolean =>
        val (qualTerm, qualExpr, qualTypeVars) = processPropExpr(qual, bound)
        val term = Select.unique(qualTerm, "unary_!")
        val expr = Cases(qualExpr, List(
          ast.Match(Constructor.True, List.empty) -> Data(Constructor.False, List.empty),
          ast.Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))
        (term, expr, qualTypeVars)

      case If(cond, thenBranch, elseBranch) =>
        val (condTerm, condExpr, condTypeVars) = processPropExpr(cond, bound)
        val (thenTerm, thenExpr, thenTypeVars) = processPropExpr(thenBranch, bound)
        val (elseTerm, elseExpr, elseTypeVars) = processPropExpr(elseBranch, bound)
        val term = If(condTerm, thenTerm, elseTerm)
        val expr = Cases(condExpr, List(
          ast.Match(Constructor.True, List.empty) -> thenExpr,
          ast.Match(Constructor.False, List.empty) -> elseExpr))
        (term, expr, condTypeVars ++ thenTypeVars ++ elseTypeVars)

      case Apply(_, _) =>
        val ctor = term match
          case Apply(TypeApply(Select(qual, "apply"), targs), args) =>
            dataConstructor(qual) map { ctor =>
              (ctor, args, (args: List[Term]) => Select.unique(qual, "apply").appliedToTypeTrees(targs).appliedToArgs(args))
            }
          case Apply(Select(qual, "apply"), args) =>
            dataConstructor(qual) map { ctor =>
              (ctor, args, (args: List[Term]) => Select.unique(qual, "apply").appliedToArgs(args))
            }
          case _ =>
            None

        ctor match
          case Some(ctor, args, make) =>
            val (argTerms, argExprs, argTypeVars) = (args map { processPropExpr(_, bound) }).unzip3
            val expr = Data(ctor, argExprs)
            (make(argTerms), expr, argTypeVars.flatten.toSet)

          case _ =>
            val (fun, args, props, make) = term match
              case Apply(Select(fun, "apply"), List(Apply(tupleApply, args))) if fun.tpe <:< propertyFunction =>
                val props = fun.tpe.asType match
                  case '[ p := (a, b) =>: r ] => properties[p]
                (fun, args, props, (fun: Term, args: List[Term]) => Select.unique(fun, "apply").appliedTo(tupleApply.appliedToArgs(args)))
              case Apply(Select(fun, "apply"), args) if isFunctionType(fun.tpe.widenTermRefByName) =>
                (fun, args, Set.empty, (fun: Term, args: List[Term]) => Select.unique(fun, "apply").appliedToArgs(args))
              case Apply(fun, args) =>
                (fun, args, Set.empty, (fun: Term, args: List[Term]) => fun.appliedToArgs(args))

            val (funTerm, funExpr, funTypeVars) = processPropExpr(fun, bound)
            val (argTerms, argExprs, argTypeVars) = (args map { processPropExpr(_, bound) }).unzip3
            val expr =
              if props.nonEmpty then
                argExprs.tail.foldLeft(App(props, funExpr, argExprs.head)) { App(Set.empty, _, _) }
              else
                argExprs.foldLeft(funExpr) { App(Set.empty, _, _) }
            (make(funTerm, argTerms), expr, funTypeVars ++ argTypeVars.flatten)

      case TypeApply(fun, args) =>
        val (funTerm, funExpr, funTypeVars) = processPropExpr(fun, bound)
        val (argTypes, argTypeVars) = (args map { arg => makeType(arg.tpe, arg.pos) }).unzip
        val expr = argTypes.foldLeft(funExpr) { TypeApp(_, _) }
        (funTerm.appliedToTypeTrees(args), expr, funTypeVars ++ argTypeVars.flatten)

      case Block(stats, expr) =>
        val (statsResult, statsTypeVars, statsBound) =
          stats.foldLeft(List.empty[(Definition, ast.Term)], Set.empty[scala.Symbol], bound) {
            case ((results, typeVars, bound), valDef @ ValDef(name, tpt, Some(rhs))) =>
              val (rhsTerm, rhsExpr, rhsTypeVars) = processPropExpr(rhs, bound)
              ((ValDef.copy(valDef)(name, tpt, Some(rhsTerm)) -> rhsExpr) :: results, typeVars ++ rhsTypeVars, bound + valDef.symbol)
            case (_, stat) =>
              report.errorAndAbort("Statements not supported", stat.pos)
          }

        val (exprTerm, exprExpr, exprTypeVars) = processPropExpr(expr, statsBound)

        val resultTerms -> resultExpr = statsResult.foldRight(List.empty[Definition] -> exprExpr) {
          case (definition -> expr, resultTerms -> resultExpr) =>
            (definition :: resultTerms) -> Cases(expr, List(ast.Bind(scala.Symbol(definition.name)) -> resultExpr))
        }

        (Block.copy(term)(resultTerms, exprTerm), resultExpr, statsTypeVars ++ exprTypeVars)

      case Match(selector, cases) =>
        def makePattern(pattern: Tree): (Pattern, Set[Symbol]) = pattern match
          case Unapply(_, _ :: _, _) =>
            report.errorAndAbort("Implicit values in patterns not supported", pattern.pos)
          case Unapply(fun, _, patterns) =>
            val ctor = fun match
              case TypeApply(Select(fun, "unapply"), _) => dataConstructor(fun)
              case Select(fun, "unapply") => dataConstructor(fun)
              case _ => None
            ctor match
              case Some(ctor) =>
                val (args, symbols) = (patterns map makePattern).unzip
                ast.Match(ctor, args) -> symbols.flatten.toSet
              case _ =>
                report.errorAndAbort("Pattern matching on non-algebraic data type not supported", pattern.pos)
          case Bind(name, Wildcard()) =>
            ast.Bind(scala.Symbol(name)) -> Set(pattern.symbol)
          case Bind(_, TypedOrTest(_, tpt))  if tpt.pos.sourceCode exists { _.nonEmpty } =>
            report.errorAndAbort("Type checks not supported", pattern.pos)
          case Bind(_, _) =>
            report.errorAndAbort("Named patterns not supported", pattern.pos)
          case Alternatives(_) =>
            report.errorAndAbort("Alternative patterns not supported", pattern.pos)
          case TypedOrTest(_, tpt) if tpt.pos.sourceCode exists { _.nonEmpty } =>
            report.errorAndAbort("Type checks not supported", pattern.pos)
          case TypedOrTest(expr, _) =>
            makePattern(expr)
          case Wildcard() =>
            ast.Bind(scala.Symbol("_")) -> Set.empty
          case pattern: Term =>
            dataConstructor(pattern) match
              case Some(ctor) =>
                ast.Match(ctor, List.empty) -> Set.empty
              case _ =>
                report.errorAndAbort("Pattern matching on non-algebraic data type not supported", pattern.pos)
          case _ =>
            report.errorAndAbort("Unsupported pattern", pattern.pos)

        val (selectorTerm, selectorExpr, selectorTypeVars) = processPropExpr(selector, bound)

        val (caseTerms, caseExprs, caseTypeVars) = (cases map {
          case CaseDef(_, Some(guard), _) =>
            report.errorAndAbort("Pattern guards not supported", guard.pos)
          case caseDef @ CaseDef(pattern, guard, rhs) =>
            val (patternPattern, patternBound) = makePattern(pattern)
            val (rhsTerm, rhsExpr, rhsTypeVars) = processPropExpr(rhs, bound ++ patternBound)
            (CaseDef.copy(caseDef)(pattern, guard, rhsTerm), patternPattern -> rhsExpr, rhsTypeVars)
        }).unzip3

        (Match.copy(term)(selectorTerm, caseTerms), Cases(selectorExpr, caseExprs), selectorTypeVars ++ caseTypeVars.flatten)

      case _ =>
        dataConstructor(term) match
          case Some(ctor) =>
            (term, Data(ctor, List.empty), Set.empty)
          case _ =>
            report.errorAndAbort("Unsupported expression", term.pos)
  end processPropExpr

  def processPropDef[T: Type](using Quotes)(
      term: quotes.reflect.Term,
      bound: Set[quotes.reflect.Symbol],
      recursive: Boolean): (quotes.reflect.Term, Option[quotes.reflect.Symbol], ast.Term, Set[scala.Symbol]) =
    import quotes.reflect.*

    def maybeFail[T: Type](pos: Position, recursive: Boolean) =
      def fail() = report.errorAndAbort(s"Unexpected term for type: ${printType[T]}", pos)

      def maybeFail[U: Type]: Unit =
        Type.of[U] match
          case '[ p := (a, b) =>: r ] => fail()
          case _ =>
        functionType[U] match
          case Some(_, '[ u ]) => maybeFail[u]
          case _ =>

      if recursive then fail() else maybeFail[T]
    end maybeFail

    term match
      case Block(List(defDef @ DefDef(name, List(TermParamClause(params)), tpt, Some(rhs))), Closure(meth, _))
          if defDef.symbol == meth.symbol =>
        val paramSymbols = params map { _.symbol }

        def makeLambda[R: Type] =
          val (lambdaBody, _, exprBody, typeVars) = processPropDef[R](rhs, bound ++ paramSymbols, recursive = false)
          val lambda = Lambda(
            defDef.symbol.owner,
            MethodType(params map { _.name })(_ => params map { _.tpt.tpe }, _ => TypeRepr.of[R]),
            (symbol, args) =>
              val paramTerms = args map { case arg: Term => arg }
              replaceRecursiveCall((paramSymbols zip paramTerms).toMap, lambdaBody, symbol))
          val (expr, vars) = params.foldRight(exprBody -> typeVars) { case (param, (expr, typeVars)) =>
            val (tpe, vars) = makeType(param.tpt.tpe, param.pos)
            Abs(Set.empty, scala.Symbol(param.name), tpe, expr) -> (typeVars ++ vars)
          }
          (lambda, expr, vars)

        if recursive then
          val (result, _, expr, typeVars) = processPropDef[T](rhs, bound ++ paramSymbols, recursive = false)
          (result, Some(params.head.symbol), expr, typeVars)
        else
          functionType[T] match
            case Some(_, '[ t ]) =>
              val (lambda, expr, typeVars) = makeLambda[t]
              (lambda, None, expr, typeVars)

            case _ =>
              Type.of[T] match
                case '[ p := (a, b) =>: r ] =>
                  val (lambda, Abs(_, ident, tpe, expr), typeVars) = makeLambda[r]: @unchecked
                  val result = '{
                    new Unchecked.AnnotatedFunction[Unchecked.PropertyAnnotation[p, (a, b)], r]:
                      val a: Unchecked.PropertyAnnotation[p, (a, b)] { type Arguments = (a, b) } =
                        new Unchecked.PropertyAnnotation[p, (a, b)] { type Arguments = (a, b) }
                      def apply(v: (a, b)): r = ${lambda.asExprOf[(a, b) => r]}(v._1, v._2)
                  }.asTerm
                  (result, None, Abs(properties[p], ident, tpe, expr), typeVars)

                case _ =>
                  maybeFail[T](term.pos, recursive)
                  val (result, expr, typeVars) = processPropExpr(term, bound)
                  (result, None, expr, typeVars)

      case _ =>
        maybeFail[T](term.pos, recursive)
        val (result, expr, typeVars) = processPropExpr(term, bound)
        (result, None, expr, typeVars)
  end processPropDef

  def makeType(using Quotes)(tpe: quotes.reflect.TypeRepr, pos: quotes.reflect.Position) =
    import quotes.reflect.*

    def fail(tpe: TypeRepr, algebraicBaseType: Option[TypeRepr]) =
      algebraicBaseType match
        case Some(algebraicBaseType) =>
          report.errorAndAbort(s"Unsupported type: ${tpe.show(using Printer.TypeReprShortCode)}. " +
            s"Subtype of: ${algebraicBaseType.show(using Printer.TypeReprShortCode)}.", pos)
        case _ =>
          report.errorAndAbort(s"Unsupported type: ${tpe.show(using Printer.TypeReprShortCode)}. " +
            "Neither function nor algebraic data type.", pos)

    def makeType(tpe: TypeRepr, types: List[TypeRepr], algebraicBaseType: Option[TypeRepr])
    : (List[TypeRepr], Set[String], List[(TypeRepr, scala.Symbol)] => ast.Type) =
      val basis = tpe.dealias.widenByName
      if types exists { _ =:= basis } then
        (List(basis),
         Set.empty,
         variables => (variables collectFirst {
           case (variableType, variableIdent) if variableType =:= basis => TypeVar(variableIdent)
         }).get)
      else
        basis match
          case TypeRef(NoPrefix(), name) if algebraicBaseType.isEmpty && basis.typeSymbol.isTypeParam =>
            (List.empty, Set(name), _ => TypeVar(scala.Symbol(name)))

          case ParamRef(binder, paramNum) if algebraicBaseType.isEmpty =>
            val name = binder match
              case MethodType(paramNames, _, _) => paramNames(paramNum)
              case PolyType(paramNames, _, _) => paramNames(paramNum)
              case _ => fail(tpe, algebraicBaseType)
            (List.empty, Set(name), _ => TypeVar(scala.Symbol(name)))

          case AppliedType(_, List(AppliedType(_, List(props, AppliedType(_, List(a, b)))), r))
              if algebraicBaseType.isEmpty &&
                 basis <:< TypeRepr.of[Any := (Nothing, Nothing) =>: _] =>
            val (aTypes, aNames, aMake) = makeType(a, types, None)
            val (bTypes, bNames, bMake) = makeType(b, types, None)
            val (rTypes, rNames, rMake) = makeType(r, types, None)
            (aTypes ++ bTypes ++ rTypes,
             aNames ++ bNames ++ rNames,
             variables => Function(aMake(variables), Function(bMake(variables), rMake(variables))))

          case AppliedType(_, args)
              if algebraicBaseType.isEmpty && isFunctionType(basis) =>
            args.init.foldRight(makeType(args.last, types, None)) {
              case (arg, (argsTypes, argsNames, argsMake)) =>
                val (argTypes, argNames, argMake) = makeType(arg, types, None)
                (argsTypes ++ argTypes, argsNames ++ argNames, variables => Function(argMake(variables), argsMake(variables)))
            }

          case MethodType(_, paramTypes, resType) if algebraicBaseType.isEmpty =>
            paramTypes.foldRight(makeType(resType, types, None)) {
              case (param, (paramsTypes, paramsNames, paramsMake)) =>
                val (paramTypes, paramNames, paramMake) = makeType(param, types, None)
                (paramsTypes ++ paramTypes, paramsNames ++ paramNames, variables => Function(paramMake(variables), paramsMake(variables)))
            }

          case PolyType(paramNames, _, resType) if algebraicBaseType.isEmpty =>
            val (resTypes, resNames, resMake) = makeType(resType, types, None)
            (resTypes,
             resNames -- paramNames,
             variables => paramNames.foldRight(resMake(variables)) { (param, res) => Universal(scala.Symbol(param), res) })

          case _ =>
            algebraic(basis) match
              case Algebraic.Sum(elements) =>
                val (elemTypes, elemNames, elemMake) = (elements map { makeType(_, basis :: types, Some(tpe)) }).unzip3
                (elemTypes.flatten,
                 elemNames.flatten.toSet,
                 variables =>
                   val sum = Sum(elemMake flatMap { make =>
                     make(variables) match
                       case Sum(sum) => sum
                       case recursive: Recursive =>
                         unfold(recursive) match
                           case Some(Sum(sum)) => sum
                           case _ => fail(tpe, algebraicBaseType)
                       case _ => fail(tpe, algebraicBaseType)
                   })
                   if elemTypes exists { _ exists { _ =:=  basis } } then
                     Recursive(
                       (variables collectFirst {
                         case (variableType, variableIdent) if variableType =:= basis => variableIdent
                       }).get,
                       sum)
                   else
                     sum)

              case Algebraic.Product(elements) =>
                val (elemTypes, elemNames, elemMake) = (elements map { makeType(_, types, None) }).unzip3
                (elemTypes.flatten,
                 elemNames.flatten.toSet,
                 variables =>
                   Sum(List(Constructor(scala.Symbol(productName(basis))) -> (elemMake map { _(variables) }))))

              case _ =>
                fail(tpe, algebraicBaseType)
    end makeType

    val (types, names, make) = makeType(tpe, List.empty, None)
    val (variables, _) = types.foldRight(List.empty[(TypeRepr, scala.Symbol)], names) {
      case (tpe, variablesNames @ (variables, names)) =>
        if !(variables exists { (variableType, _) => variableType =:= tpe }) then
          val name = Naming.freshIdent("X", names)
          (tpe -> scala.Symbol(name) :: variables) -> (names + name)
        else
          variablesNames
    }
    (make(variables), names map { scala.Symbol(_) })
  end makeType

  enum Algebraic[+T]:
    case Sum[T](elements: List[T]) extends Algebraic[T]
    case Product[T](elements: List[T]) extends Algebraic[T]
    case None extends Algebraic[Nothing]

  def algebraic(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    import quotes.reflect.*

    def typeList[T: Type]: List[TypeRepr] = Type.of[T] match
      case '[ t *: ts ] => TypeRepr.of[t] :: typeList[ts]
      case _ => Nil

    tpe.asType match
      case '[ true ] =>
        Algebraic.Product(List.empty)
      case '[ false ] =>
        Algebraic.Product(List.empty)
      case '[ Boolean ] =>
        Algebraic.Sum(List(TypeRepr.of[true], TypeRepr.of[false]))
      case '[ t ] =>
        Expr.summon[Mirror.Of[t]] match
          case Some('{ $m: Mirror.Sum { type MirroredElemTypes = t } }) =>
            Algebraic.Sum(typeList[t])
          case Some('{ $m: Mirror.Product { type MirroredElemTypes = t } }) =>
            Algebraic.Product(typeList[t])
          case _ =>
            Algebraic.None
  end algebraic

  def isAlgebraic(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    algebraic(tpe) != Algebraic.None

  def isSum(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    algebraic(tpe) match
      case Algebraic.Sum(_) => true
      case _ => false

  def isProduct(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    algebraic(tpe) match
      case Algebraic.Product(_) => true
      case _ => false

  def productName(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    import quotes.reflect.*

    def termSymbol(tpe: TypeRepr) =
      if tpe.termSymbol.exists then
        tpe.termSymbol
      else if tpe.typeSymbol.companionModule.exists then
        tpe.typeSymbol.companionModule
      else
        tpe.typeSymbol

    tpe.dealias match
      case ConstantType(BooleanConstant(true)) =>
        Constructor.True.ident.name
      case ConstantType(BooleanConstant(false)) =>
        Constructor.False.ident.name
      case tpe: NamedType =>
        s"${termSymbol(tpe.qualifier).fullName}.${termSymbol(tpe).name}"
      case tpe =>
        termSymbol(tpe).fullName
  end productName

  def replaceRecursiveCall(using Quotes)(
      substs: Map[quotes.reflect.Symbol, quotes.reflect.Term],
      term: quotes.reflect.Term,
      owner: quotes.reflect.Symbol) =
    import quotes.reflect.*

    class RecursiveCallReplacer(substs: Map[Symbol, Term]) extends TreeMap:
      override def transformTerm(term: Term)(owner: Symbol) =
        substs.getOrElse(term.symbol, super.transformTerm(term)(owner))

    RecursiveCallReplacer(substs).transformTerm(term.changeOwner(owner))(owner)
  end replaceRecursiveCall

  def properties[T: Type](using Quotes): Properties =
    import quotes.reflect.*

    val tpe = TypeRepr.of[T]
    if !(TypeRepr.of[Comm & Assoc & Idem & Sel & Refl & Irefl & Sym & Antisym & Asym & Conn & Trans] <:< tpe) then
      report.errorAndAbort(s"Unknown property: ${printType[T]}")

    val properties = List(
      TypeRepr.of[Comm] -> Commutative,
      TypeRepr.of[Assoc] -> Associative,
      TypeRepr.of[Idem] -> Idempotent,
      TypeRepr.of[Sel] -> Selection,
      TypeRepr.of[Refl] -> Reflexive,
      TypeRepr.of[Irefl] -> Irreflexive,
      TypeRepr.of[Sym] -> Symmetric,
      TypeRepr.of[Antisym] -> Antisymmetric,
      TypeRepr.of[Asym] -> Asymmetric,
      TypeRepr.of[Conn] -> Connected,
      TypeRepr.of[Trans] -> Transitive)

    (properties collect { case (propertyType, property) if tpe <:< propertyType => property }).toSet
  end properties

  def printType[T: Type](using Quotes): String =
    import quotes.reflect.*

    functionType[T] match
      case Some(args, '[ t ]) =>
        s"(${(args map { printType(using _, quotes) }).mkString("(", ", ", ")")} => ${printType[t]})"
      case _ =>
        Type.of[T] match
          case '[ Nothing ] =>
            TypeRepr.of[T].show(using Printer.TypeReprShortCode)
          case '[ p := (a, b) =>: r ] =>
            s"(${printType[p]} := (${printType[a]}, ${printType[b]}) =>: ${printType[r]})"
          case _ =>
            TypeRepr.of[T].show(using Printer.TypeReprShortCode)
  end printType

  def isFunctionType[T: Type](using Quotes): Boolean =
    isFunctionType(quotes.reflect.TypeRepr.of[T])

  def isFunctionType(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    tpe.isFunctionType && !tpe.isDependentFunctionType && !tpe.isContextFunctionType && !tpe.isErasedFunctionType

  def functionType[T: Type](using Quotes): Option[(List[Type[? <: Any]], Type[? <: Any])] =
    import quotes.reflect.*

    def toType(tpe: TypeRepr) = tpe.asType match
      case '[ t ] => Type.of[t]

    functionType(TypeRepr.of[T]) map { (args, result) =>
      (args map { toType(_) }, toType(result))
    }
  end functionType

  def functionType(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    tpe match
      case quotes.reflect.AppliedType(_, args) if isFunctionType(tpe) => Some(args.init, args.last)
      case _ => None
end Checked
