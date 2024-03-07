package propel
package dsl.impl

import ast.{Type => _, Term => _, Property => _, dsl => _, *}
import typer.*

import dsl.scala.{=:= => _, *}

import scala.collection.immutable.{ListMap, ListSet}
import scala.collection.mutable
import scala.deriving.Mirror
import scala.quoted.*

class Checked(normalization: List[evaluator.properties.Normalization]) extends scala.annotation.Annotation

object Checked:
  extension [A, B, C, D, E](list: List[(A, B, C, D, E)]) private def unzip5 =
    list.foldRight(List.empty[A], List.empty[B], List.empty[C], List.empty[D], List.empty[E]) {
      case ((elementA, elementB, elementC, elementD, elementE), (listA, listB, listC, listD, listE)) =>
       (elementA :: listA, elementB :: listB, elementC :: listC, elementD :: listD, elementE :: listE)
    }

  def check[T: Type](f: Expr[Any], recursive: Boolean)(using Quotes) =
    import quotes.reflect.*

    val Inlined(_, List(), Typed(fTerm, _)) = f.asTerm: @unchecked
    val (result, recursiveSymbol, expr, typeVars, propVars, external, _) =
      processPropDef[T](fTerm, Symbol.spliceOwner, Set.empty, mutable.Map.empty, None, recursive)
    val externalProperties = external.toList flatMap auxiliaryProperties

    def reportErrors(expr: ast.Term) =
      val errors = expr.errors
      if errors.nonEmpty then
        report.errorAndAbort((errors map { case (_, Error(message)) => message }).mkString("", "\n\n", ""))

    def typeAbs(expr: ast.Term, typeVars: Set[scala.Symbol]) =
      typeVars.foldRight(expr) { TypeAbs(_, _) }

    def checkProperties(expr: ast.Term) =
      val recursiveExpr = recursiveSymbol match
        case Some(recursiveSymbol) =>
          val (tpe @ Function(t, u), _) = makeType(TypeRepr.of[T], Position.ofMacroExpansion): @unchecked
          typeAbs(
            App(Set.empty,
              TypeApp(TypeApp(zCombinator, t), u),
              Abs(Set.empty, scala.Symbol(recursiveSymbol.name), tpe, expr)),
            typeVars)
        case _ =>
          typeAbs(expr, typeVars)

      val checked = evaluator.properties.check(recursiveExpr, assumedUncheckedConjectures = externalProperties)
      reportErrors(checked)
      checked
    end checkProperties

    val checked = checkProperties(expr(Map.empty))

    propVars foreach { (symbol, properties) =>
      properties foreach { property =>
        checkProperties(expr(Map(symbol -> Set(property))))
      }
    }

    val (resultType, annotatedResultType) = resultTypeWithProperties(checked, TypeRepr.of[T], typeVars.size)

    (resultType.asType, annotatedResultType.asType) match
      case '[ r ] -> '[ a ] =>
        recursiveSymbol match
          case Some(recursiveSymbol) =>
            val Inlined(_, List(), Block(List(recursiveDefinition), _)) = '{ var rec: r = null.asInstanceOf[r] }.asTerm: @unchecked
            val recursiveCall = Ref(recursiveDefinition.symbol)

            Typed(
              Block(
                List(
                  recursiveDefinition,
                  Assign(
                    recursiveCall,
                    replaceRecursiveCall(Map(recursiveSymbol -> recursiveCall), result, Symbol.spliceOwner))),
                recursiveCall),
              TypeTree.of[a]).asExprOf[T]

          case _ =>
            Typed(result, TypeTree.of[a]).asExprOf[T]
  end check

  val zCombinator =
    import ast.dsl.*
    tpabs("T", "U")(abs("f" -> tp(("T" -> "U") -> ("T" -> "U")))(
      abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v")),
      abs("x" -> rec("X")("X" -> ("T" -> "U")))("f", abs("v" -> tp("T"))(("x", "x"), "v"))))

  def checkedAnnotation(using Quotes)(term: quotes.reflect.Term) =
    import quotes.reflect.*
    term.tpe.widenTermRefByName match
      case AppliedType(_, args) => args.last match
        case AnnotatedType(_, annotation) if annotation.tpe <:< TypeRepr.of[Checked] => Some(annotation)
        case _ => None
      case _ => None

  def auxiliaryProperties(using Quotes)(term: quotes.reflect.Term) =
    checkedAnnotation(term).fold(List.empty) { checkedAnnotation =>
      val normalizations =
        checkedAnnotation.asExpr match
          case '{ Checked(${Expr(normalizations)}) } => normalizations
          case '{ new Checked(${Expr(normalizations)}) } => normalizations
          case _ => List.empty

      val ident = Symbol(term.symbol.fullName)

      normalizations map { case evaluator.properties.Normalization(pattern, result, abstraction, variables, reversible) =>
        evaluator.properties.Normalization(
          subst(pattern, Map(abstraction -> Var(ident))),
          subst(result, Map(abstraction -> Var(ident))),
          ident,
          variables,
          reversible)
      }
    }

  def resultTypeWithProperties(using Quotes)(expr: ast.Term, resultType: quotes.reflect.TypeRepr, typeAbsPrefixLength: Int) =
    import quotes.reflect.*

    def derivedProperties(term: ast.Term): Map[Abstraction, evaluator.properties.Derived] = term match
      case Abs(_, _, _, expr) =>
        derivedProperties(expr) ++ (term.info(Abstraction) flatMap { abstraction =>
          term.info(evaluator.properties.Derived) map { abstraction -> _ }
        })
      case App(_, expr, arg) =>
        derivedProperties(expr) ++ derivedProperties(arg)
      case TypeAbs(_, expr) =>
        derivedProperties(expr)
      case TypeApp(expr, _) =>
        derivedProperties(expr)
      case Data(_, args) =>
        (args flatMap derivedProperties).toMap
      case Var(_) =>
        Map.empty
      case Cases(scrutinee, cases) =>
        derivedProperties(scrutinee) ++ (cases flatMap { (_, expr) => derivedProperties(expr) })

    val abstractionProperties = derivedProperties(expr)

    def skipTypeAbs(tpe: ast.Type, typeAbsPrefixLength: Int): ast.Type =
      tpe match
        case Universal(_, expr) if typeAbsPrefixLength > 0 =>
          skipTypeAbs(expr, typeAbsPrefixLength - 1)
        case _ =>
          tpe

    def extendAlgebraicProperties(tpe: ast.Type, resultType: TypeRepr, argIndex: Int): TypeRepr =
      tpe -> resultType match
        case Function(a0, Function(b0, r0)) ->
             AppliedType(tycon0, List(AppliedType(tycon1, List(props, AppliedType(tycon2, List(a1, b1)))), r1))
            if argIndex == 0 && resultType <:< TypeRepr.of[Any := (Nothing, Nothing) =>: _] =>
          val updatedProps =
            (tpe.info(Abstraction) flatMap { abstractionProperties.get(_) }).fold(props) { derived =>
              val (specifiedProperties, _) = properties(props)
              val additonalProperties = derived.properties -- specifiedProperties map property
              if additonalProperties.nonEmpty && props =:= TypeRepr.of[Any] then
                additonalProperties.reduceLeft { AndType(_, _) }
              else
                additonalProperties.foldLeft(props) { AndType(_, _) }
            }

          AppliedType(tycon0, List(
            AppliedType(tycon1, List(
              updatedProps,
              AppliedType(tycon2, List(
                extendAlgebraicProperties(a0, a1, 0),
                extendAlgebraicProperties(b0, b1, 0))))),
            extendAlgebraicProperties(r0, r1, 0)))

        case Function(a0, r0) -> AppliedType(tycon, args) if isFunctionType(resultType) =>
          val rest = args.size - argIndex
          if rest <= 1 then
            resultType
          else if rest == 2 then
            val (init, List(a1, r1)) = args.splitAt(argIndex)
            AppliedType(tycon, init ++ List(
              extendAlgebraicProperties(a0, a1, 0),
              extendAlgebraicProperties(r0, r1, 0)))
          else
            val r1 = AppliedType(tycon, args.updated(argIndex, extendAlgebraicProperties(a0, args(argIndex), 0)))
            extendAlgebraicProperties(r0, r1, argIndex + 1)

        case _ =>
          resultType
    end extendAlgebraicProperties

    val (extendedResultType, normalizations) =
      (expr.termType map { skipTypeAbs(_, typeAbsPrefixLength) }).fold(resultType -> List.empty) { tpe =>
        extendAlgebraicProperties(tpe, resultType, 0) ->
        (tpe.info(Abstraction) flatMap { abstractionProperties.get(_) }).fold(List.empty) { _.normalizations }
      }

    extendedResultType match
      case AppliedType(tycon, args) =>
        val Inlined(_, List(), annotation) = '{ Checked(${Expr(normalizations)}) }.asTerm: @unchecked
        extendedResultType -> AppliedType(tycon, args.init :+ AnnotatedType(args.last, annotation))
      case _ =>
        extendedResultType -> extendedResultType
  end resultTypeWithProperties

  def processPropExpr(using Quotes)(
      term: quotes.reflect.Term,
      bound: Set[quotes.reflect.Symbol],
      externalTerms: mutable.Map[scala.Symbol, ast.Term],
      bindingNamePrefix: String = "")
    : (quotes.reflect.Term,
       Map[quotes.reflect.Symbol, Properties] => ast.Term,
       Set[scala.Symbol],
       ListMap[quotes.reflect.Symbol, Properties],
       ListSet[quotes.reflect.Term]) =
    import quotes.reflect.*

    type VarProps = Map[quotes.reflect.Symbol, Properties]

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

    def simplify(cases: Cases) = cases match
      case Cases(scrutinee: Var, List(ast.Bind(ident) -> expr)) =>
        subst(expr, Map(ident -> scrutinee))
      case Cases(scrutinee, List(ast.Bind(ident) -> expr)) =>
        expr.syntacticInfo.freeVars.getOrElse(ident, 0) match
          case 0 => expr
          case 1 => subst(expr, Map(ident -> scrutinee))
          case _ => cases
      case _ =>
        cases

    term match
      case Inlined(call, List(), body) =>
        val (bodyTerm, bodyExpr, bodyTypeVars, bodyPropVars, bodyExternal) = processPropExpr(body, bound, externalTerms)
        (Inlined.copy(term)(call, List(), bodyTerm), bodyExpr, bodyTypeVars, bodyPropVars, bodyExternal)

      case Inlined(Some(call), bindings, expr) if call.symbol.owner == TypeRepr.of[prop.type].typeSymbol =>
        val (exprTerm, exprExpr, exprTypeVars, exprPropVars, exprExternal) = processPropExpr(expr, bound, externalTerms)
        (Inlined(Some(call), bindings, expr), exprExpr, exprTypeVars, exprPropVars, exprExternal)

      case Block(List(), expr) =>
        processPropExpr(expr, bound, externalTerms)

      case Typed(expr, tpt) if !checkedAnnotation(expr).isDefined && checkedAnnotation(term).isDefined && expr.tpe =:= tpt.tpe =>
        def makeIdent(index: Int): scala.Symbol =
          val ident = scala.Symbol(s"<${bindingNamePrefix}property-checked/$index>")
          if externalTerms contains ident then makeIdent(index + 1) else ident
        val ident = makeIdent(0)
        val stub = Ref(Symbol.newVal(defn.RootClass, ident.name, tpt.tpe, Flags.EmptyFlags, Symbol.noSymbol))
        val (tpe, typeVars) = makeType(term.tpe.widenTermRefByName, term.pos)
        val expr = Var(ident).withExtrinsicInfo(Typing.Specified(Right(Abstraction.assign(tpe))))
        externalTerms += ident -> expr
        (term, _ => expr, typeVars, ListMap.empty, ListSet(stub))

      case Typed(expr, tpt) =>
        val (exprTerm, exprExpr, exprTypeVars, exprPropVars, exprExternal) = processPropExpr(expr, bound, externalTerms)
        (Typed(exprTerm, tpt), exprExpr, exprTypeVars, exprPropVars, exprExternal)

      case Ident(name) if bound contains term.symbol =>
        (term, _ => Var(scala.Symbol(name)), Set.empty, ListMap.empty, ListSet.empty)

      case term: Ref if hasStableOuterReferencePath(term) =>
        dataConstructor(term) match
          case Some(ctor) =>
            (term, _ => Data(ctor, List.empty), Set.empty, ListMap.empty, ListSet.empty)
          case _ =>
            val (tpe, typeVars) = makeType(term.tpe.widenTermRefByName, term.pos)
            val ident = scala.Symbol(term.symbol.fullName)
            val expr = externalTerms.getOrElseUpdate(ident, Var(ident).withExtrinsicInfo(Typing.Specified(Right(Abstraction.assign(tpe)))))
            (term, _ => expr, typeVars, ListMap.empty, ListSet(term))

      case Apply(select @ Select(qual, name @ ("==" | "!=")), List(arg))
          if (qual.tpe.widenTermRefByName <:< arg.tpe.widenTermRefByName ||
              arg.tpe.widenTermRefByName <:< qual.tpe.widenTermRefByName) &&
             isAlgebraic(qual.tpe.widenTermRefByName) &&
             isAlgebraic(arg.tpe.widenTermRefByName) =>
        val (qualTerm, qualExpr, qualTypeVars, qualPropVars, qualExternal) = processPropExpr(qual, bound, externalTerms)
        val (argTerm, argExpr, argTypeVars, argPropVars, argExternal) = processPropExpr(arg, bound, externalTerms)
        val (tpe, typeVars) =
          if qual.tpe.widenTermRefByName <:< arg.tpe.widenTermRefByName then
            makeType(arg.tpe.widenTermRefByName, select.pos)
          else
            makeType(qual.tpe.widenTermRefByName, select.pos)
        val term = qualTerm.select(select.symbol).appliedTo(argTerm)
        val expr = (varProps: VarProps) =>
          val booleanType = Sum(List(Constructor.True -> List.empty, Constructor.False -> List.empty))
          val relationType = Function(tpe, Function(tpe, booleanType))
          val relationExpr = App(Set.empty,
            App(Set(Reflexive, Symmetric, Antisymmetric, Transitive),
              Var(scala.Symbol("<synthetic algebraic equality>")).withExtrinsicInfo(Typing.Specified(Right(relationType))),
              qualExpr(varProps)),
            argExpr(varProps))
          name match
            case "==" => relationExpr
            case "!=" => Cases(relationExpr, List(
              ast.Match(Constructor.True, List.empty) -> Data(Constructor.False, List.empty),
              ast.Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))
        (term, expr, qualTypeVars ++ argTypeVars ++ typeVars, qualPropVars ++ argPropVars, qualExternal ++ argExternal)

      case Apply(TypeApply(Select(qual, "::"), targs), List(arg)) if qual.tpe <:< list =>
        val (qualTerm, qualExpr, qualTypeVars, qualPropVars, qualExternal) = processPropExpr(qual, bound, externalTerms)
        val (argTerm, argExpr, argTypeVars, argPropVars, argExternal) = processPropExpr(arg, bound, externalTerms)
        val term = Select.unique(qualTerm, "::").appliedToTypeTrees(targs).appliedTo(argTerm)
        val expr = (varProps: VarProps) => Data(cons, List(argExpr(varProps), qualExpr(varProps)))
        (term, expr, qualTypeVars ++ argTypeVars, qualPropVars ++ argPropVars, qualExternal ++ argExternal)

      case Apply(Select(qual, name @ ("&&" | "||")), List(arg)) if qual.tpe <:< boolean =>
        val (qualTerm, qualExpr, qualTypeVars, qualPropVars, qualExternal) = processPropExpr(qual, bound, externalTerms)
        val (argTerm, argExpr, argTypeVars, argPropVars, argExternal) = processPropExpr(arg, bound, externalTerms)
        val term = Select.unique(qualTerm, name).appliedTo(argTerm)
        val expr = (varProps: VarProps) =>
          name match
            case "&&" => Cases(qualExpr(varProps), List(
              ast.Match(Constructor.True, List.empty) -> argExpr(varProps),
              ast.Match(Constructor.False, List.empty) -> Data(Constructor.False, List.empty)))
            case "||" => Cases(qualExpr(varProps), List(
              ast.Match(Constructor.True, List.empty) -> Data(Constructor.True, List.empty),
              ast.Match(Constructor.False, List.empty) -> argExpr(varProps)))
        (term, expr, qualTypeVars ++ argTypeVars, qualPropVars ++ argPropVars, qualExternal ++ argExternal)

      case Select(qual, "unary_!") if qual.tpe <:< boolean =>
        val (qualTerm, qualExpr, qualTypeVars, qualPropVars, qualExternal) = processPropExpr(qual, bound, externalTerms)
        val term = Select.unique(qualTerm, "unary_!")
        val expr = (varProps: VarProps) =>
          Cases(qualExpr(varProps), List(
            ast.Match(Constructor.True, List.empty) -> Data(Constructor.False, List.empty),
            ast.Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))
        (term, expr, qualTypeVars, qualPropVars, qualExternal)

      case If(cond, thenBranch, elseBranch) =>
        val (condTerm, condExpr, condTypeVars, condPropVars, condExternal) = processPropExpr(cond, bound, externalTerms)
        val (thenTerm, thenExpr, thenTypeVars, thenPropVars, thenExternal) = processPropExpr(thenBranch, bound, externalTerms)
        val (elseTerm, elseExpr, elseTypeVars, elsePropVars, elseExternal) = processPropExpr(elseBranch, bound, externalTerms)
        val term = If(condTerm, thenTerm, elseTerm)
        val expr = (varProps: VarProps) =>
          Cases(condExpr(varProps), List(
            ast.Match(Constructor.True, List.empty) -> thenExpr(varProps),
            ast.Match(Constructor.False, List.empty) -> elseExpr(varProps)))
        (term,
         expr,
         condTypeVars ++ thenTypeVars ++ elseTypeVars,
         condPropVars ++ thenPropVars ++ elsePropVars,
         condExternal ++ thenExternal ++ elseExternal)

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
            val (argTerms, argExprs, argTypeVars, argPropVars, argExternal) = (args map { processPropExpr(_, bound, externalTerms) }).unzip5
            val expr = (varProps: VarProps) => Data(ctor, argExprs map { _(varProps) })
            (make(argTerms), expr, argTypeVars.flatten.toSet, argPropVars.flatten.to(ListMap), argExternal.flatten.to(ListSet))

          case _ =>
            val (fun, args, props, propVars, make) = term match
              case Apply(Select(fun, "apply"), args) if fun.tpe <:< propertyFunction =>
                val (props, propVars) = fun.tpe.asType match
                  case '[ p := (a, b) =>: r ] =>
                    properties(TypeRepr.of[p])
                (fun, args, props, propVars, (fun: Term, args: List[Term]) => Select.unique(fun, "apply").appliedToArgs(args))
              case Apply(Select(fun, "apply"), args) if isFunctionType(fun.tpe.widenTermRefByName) =>
                (fun, args, Set.empty, ListMap.empty, (fun: Term, args: List[Term]) => Select.unique(fun, "apply").appliedToArgs(args))
              case Apply(fun, args) =>
                (fun, args, Set.empty, ListMap.empty, (fun: Term, args: List[Term]) => fun.appliedToArgs(args))

            val (funTerm, funExpr, funTypeVars, funPropVars, funExternal) = processPropExpr(fun, bound, externalTerms)
            val (argTerms, argExprs, argTypeVars, argPropVars, argExternal) = (args map { processPropExpr(_, bound, externalTerms) }).unzip5
            val expr = (varProps: VarProps) =>
              val additonalProps = (varProps.view filterKeys { propVars contains _ }).values.flatten
              if props.nonEmpty || additonalProps.nonEmpty then
                argExprs.tail.foldLeft(App(props ++ additonalProps, funExpr(varProps), argExprs.head(varProps))) { (fun, arg) =>
                  App(Set.empty, fun, arg(varProps))
                }
              else
                argExprs.foldLeft(funExpr(varProps)) { (fun, arg) =>
                  App(Set.empty, fun, arg(varProps))
                }
            (make(funTerm, argTerms),
             expr,
             funTypeVars ++ argTypeVars.flatten,
             funPropVars ++ argPropVars.flatten ++ propVars,
             funExternal ++ argExternal.flatten)

      case TypeApply(fun, args) =>
        val paramBounds = fun.tpe.widenTermRefByName match
          case PolyType(_, paramBounds, _) if paramBounds.sizeIs == args.size => paramBounds
          case _ => List.fill(args.size) { TypeBounds.empty }

        val (argTypes, argTypeVars) =
          (args zip paramBounds collect { case (arg, bound) if !isPropertyTypeBound(bound) =>
            makeType(arg.tpe, arg.pos)
          }).unzip

        val (funTerm, funExpr, funTypeVars, funPropVars, funExternal) = processPropExpr(fun, bound, externalTerms)
        val expr = (varProps: VarProps) => argTypes.foldLeft(funExpr(varProps)) { TypeApp(_, _) }
        (funTerm.appliedToTypeTrees(args), expr, funTypeVars ++ argTypeVars.flatten, funPropVars, funExternal)

      case Block(List(defDef @ DefDef(name, List(TermParamClause(params)), tpt, Some(rhs))), closure @ Closure(meth, tpe))
          if defDef.symbol == meth.symbol =>
        val paramSymbols = params map { _.symbol }
        val (rhsTerm, rhsExpr, rhsTypeVars, rhsPropVars, rhsExternal) = processPropExpr(rhs, bound ++ paramSymbols, externalTerms)

        val (paramDefinitions, paramTypeVars) = (params map { param =>
          val (tpe, typeVars) = makeType(param.tpt.tpe, param.pos)
          (scala.Symbol(param.name) -> tpe, typeVars)
        }).unzip

        val resultExpr = (varProps: VarProps) =>
          paramDefinitions.foldRight(rhsExpr(varProps)) { case ((ident, tpe), expr) => Abs(Set.empty, ident, tpe, expr) }

        val resultTerm =
          Block.copy(term)(List(DefDef.copy(defDef)(name, List(TermParamClause(params)), tpt, Some(rhsTerm))), Closure.copy(closure)(meth, tpe))

        (resultTerm, resultExpr, rhsTypeVars ++ paramTypeVars.flatten, rhsPropVars, rhsExternal)

      case Block(stats, expr) =>
        val (statsResult, statsTypeVars, statsPropVars, statsExternal, statsBound) =
          stats.foldLeft(List.empty[(Definition, VarProps => ast.Term)], Set.empty[scala.Symbol], ListMap.empty[Symbol, Properties], ListSet.empty[Term], bound) {
            case ((results, typeVars, propVars, external, bound), valDef @ ValDef(name, tpt, Some(rhs))) =>
              val (rhsTerm, rhsExpr, rhsTypeVars, rhsPropVars, rhsExternal) =
                processPropExpr(rhs, bound, externalTerms, bindingNamePrefix = s"$name:")
              ((ValDef.copy(valDef)(name, tpt, Some(rhsTerm)) -> rhsExpr) :: results,
               typeVars ++ rhsTypeVars,
               propVars ++ rhsPropVars,
               external ++ rhsExternal,
               bound + valDef.symbol)
            case (_, stat) =>
              report.errorAndAbort("Statements not supported", stat.pos)
          }

        val (exprTerm, exprExpr, exprTypeVars, exprPropVars, exprExternal) = processPropExpr(expr, statsBound, externalTerms)

        val resultTerms -> resultExpr = statsResult.foldRight(List.empty[Definition] -> exprExpr) {
          case (definition -> expr, resultTerms -> resultExpr) =>
            (definition :: resultTerms) ->
            ((varProps: VarProps) => simplify(Cases(expr(varProps), List(ast.Bind(scala.Symbol(definition.name)) -> resultExpr(varProps)))))
        }

        (Block.copy(term)(resultTerms, exprTerm),
         resultExpr,
         statsTypeVars ++ exprTypeVars,
         statsPropVars ++ exprPropVars,
         statsExternal ++ exprExternal)

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

        val (selectorTerm, selectorExpr, selectorTypeVars, selectorPropVars, selectorExternal) = processPropExpr(selector, bound, externalTerms)

        val (caseTerms, caseExprs, caseTypeVars, casePropVars, caseExternal) = (cases map {
          case CaseDef(_, Some(guard), _) =>
            report.errorAndAbort("Pattern guards not supported", guard.pos)
          case caseDef @ CaseDef(pattern, guard, rhs) =>
            val (patternPattern, patternBound) = makePattern(pattern)
            val (rhsTerm, rhsExpr, rhsTypeVars, rhsPropVars, rhsExternal) = processPropExpr(rhs, bound ++ patternBound, externalTerms)
            (CaseDef.copy(caseDef)(pattern, guard, rhsTerm),
             (varProps: VarProps) => patternPattern -> rhsExpr(varProps),
             rhsTypeVars,
             rhsPropVars,
             rhsExternal)
        }).unzip5

        (Match.copy(term)(selectorTerm, caseTerms),
         (varProps: VarProps) => simplify(Cases(selectorExpr(varProps), caseExprs map { _(varProps) })),
         selectorTypeVars ++ caseTypeVars.flatten,
         selectorPropVars ++ casePropVars.flatten,
         selectorExternal ++ caseExternal.flatten)

      case _ =>
        dataConstructor(term) match
          case Some(ctor) =>
            (term, _ => Data(ctor, List.empty), Set.empty, ListMap.empty, ListSet.empty)
          case _ =>
            report.errorAndAbort("Unsupported expression", term.pos)
  end processPropExpr

  def processPropDef[T: Type](using Quotes)(
      term: quotes.reflect.Term,
      owner: quotes.reflect.Symbol,
      bound: Set[quotes.reflect.Symbol],
      externalTerms: mutable.Map[scala.Symbol, ast.Term],
      recursiveSymbol: Option[quotes.reflect.Symbol],
      recursive: Boolean)
    : (quotes.reflect.Term,
       Option[quotes.reflect.Symbol],
       Map[quotes.reflect.Symbol, Properties] => ast.Term,
       Set[scala.Symbol],
       ListMap[quotes.reflect.Symbol, Properties],
       ListSet[quotes.reflect.Term],
       List[Map[quotes.reflect.Symbol, Properties] => ast.Term]) =
    import quotes.reflect.*

    type VarProps = Map[quotes.reflect.Symbol, Properties]

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
      case Inlined(call, List(), body) =>
        val (result, symbol, expr, typeVars, propVars, external, customProperties) =
          processPropDef[T](body, owner, bound, externalTerms, recursiveSymbol, recursive)
        (Inlined.copy(term)(call, List(), result), symbol, expr, typeVars, propVars, external, customProperties)

      case Block(List(), expr) =>
        processPropDef[T](expr, owner, bound, externalTerms, recursiveSymbol, recursive)

      case Apply(Apply(props, List(Typed(Repeated(exprs, _), _))), List(body))
          if props.symbol == Symbol.requiredMethod("propel.dsl.scala.props") =>

        val (result, symbol, expr, typeVars, propVars, external, customProperties) =
          processPropDef[T](body, owner, bound, externalTerms, recursiveSymbol, recursive)

        recursiveSymbol.fold(term, symbol, expr, typeVars, propVars, external, customProperties) { recursiveSymbol =>
          val (properties, propertiesTypeVars, propertiesExternal) = (exprs map {
            case Block(List(defDef @ DefDef(_, List(TermParamClause(params)), _, Some(Apply(Apply(equals, List(lhs)), List(rhs))))), Closure(meth, _))
                if equals.symbol == Symbol.requiredMethod("propel.dsl.scala.=:=") && defDef.symbol == meth.symbol =>
              val paramSymbols = params map { _.symbol }
              val paramNames = params map { param => scala.Symbol(param.name) }

              val (_, lhsExpr, _, _, lhsExternal) = processPropExpr(lhs, bound ++ paramSymbols, externalTerms)
              val (_, rhsExpr, _, _, rhsExternal) = processPropExpr(rhs, bound ++ paramSymbols, externalTerms)

              val (paramDefinitions, paramTypeVars) = (params map { param =>
                val (tpe, typeVars) = makeType(param.tpt.tpe, param.pos)
                (scala.Symbol(param.name) -> tpe, typeVars)
              }).unzip

              val properties = (varProps: VarProps) =>
                val body = App(Set.empty, App(Set.empty, Var(scala.Symbol("==")), lhsExpr(varProps)), rhsExpr(varProps))
                  .withExtrinsicInfo(evaluator.properties.CustomProperties(List.empty))

                val quantifiedBody =
                  paramDefinitions.foldRight(body) { case ((ident, tpe), expr) => Abs(Set.empty, ident, tpe, expr) }

                App(Set.empty, App(Set.empty, Var(scala.Symbol("prop-for")), Var(scala.Symbol(recursiveSymbol.name))), quantifiedBody)
                  .withExtrinsicInfo(evaluator.properties.CustomProperties(List.empty))

              (properties, paramTypeVars.flatten, lhsExternal ++ rhsExternal)

            case expr =>
              report.errorAndAbort("Unexpected property definition. Properties must have the shape (x₀: T₀, ..., xₙ: Tₙ) => e =:= e′", expr.pos)
          }).unzip3

          (result, symbol, expr, typeVars ++ propertiesTypeVars.flatten, propVars, external ++ propertiesExternal.flatten, properties ++ customProperties)
        }

      case Block(List(defDef @ DefDef(name, List(TermParamClause(params)), tpt, Some(rhs))), Closure(meth, _))
          if defDef.symbol == meth.symbol =>
        val paramSymbols = params map { _.symbol }
        val recursiveSymbol = Option.when(recursive) { params.head.symbol }

        def makeLambda[R: Type] =
          val (lambdaBody, _, exprBody, typeVars, propVars, external, customProperties) =
            processPropDef[R](rhs, defDef.symbol, bound ++ paramSymbols, externalTerms, recursiveSymbol, recursive = false)
          val lambda = Lambda(
            owner,
            MethodType(params map { _.name })(_ => params map { _.tpt.tpe }, _ => TypeRepr.of[R]),
            (symbol, args) =>
              val paramTerms = args map { case arg: Term => arg }
              replaceRecursiveCall((paramSymbols zip paramTerms).toMap, lambdaBody, symbol))
          val (expr, vars) = params.foldRight(exprBody -> typeVars) { case (param, (expr, typeVars)) =>
            val (tpe, vars) = makeType(param.tpt.tpe, param.pos)
            { (varProps: VarProps) => Abs(Set.empty, scala.Symbol(param.name), tpe, expr(varProps)) } -> (typeVars ++ vars)
          }
          (lambda, expr, vars, propVars, external, customProperties)

        if recursive then
          val (result, _, expr, typeVars, propVars, external, customProperties) =
            processPropDef[T](rhs, defDef.symbol, bound ++ paramSymbols, externalTerms, recursiveSymbol, recursive = false)
          val exprWithCustomProperties = (varProps: VarProps) =>
            if recursiveSymbol.isDefined && customProperties.nonEmpty then
              val ident = scala.Symbol(recursiveSymbol.get.name)
              val properties =
                customProperties.foldRight[ast.Term](Var(ident)) { (customProperty, expr) =>
                  Cases(customProperty(varProps), List(ast.Bind(scala.Symbol("_")) -> expr))
                }
              Cases(expr(varProps), List(ast.Bind(ident) -> properties))
            else
              expr(varProps)
          (result, recursiveSymbol, exprWithCustomProperties, typeVars, propVars, external, customProperties)
        else
          functionType[T] match
            case Some(_, '[ t ]) =>
              val (lambda, expr, typeVars, propVars, external, customProperties) = makeLambda[t]
              (lambda, None, expr, typeVars, propVars, external, customProperties)

            case _ =>
              Type.of[T] match
                case '[ p := (a, b) =>: r ] =>
                  val (lambda, lambdaExpr, typeVars, lambdaPropVars, external, customProperties) = makeLambda[r]
                  val Inlined(_, List(), result) = '{
                    new Unchecked.AnnotatedFunction[Unchecked.PropertyAnnotation[Nothing, (a, b)], r]:
                      def apply(v1: a, v2: b): r = ${ Expr.betaReduce('{ ${lambda.asExprOf[(a, b) => r]}(v1, v2) }) }
                  }.asTerm: @unchecked
                  val (props, propVars) = properties(TypeRepr.of[p])
                  val expr = (varProps: VarProps) =>
                    val additonalProps = (varProps.view filterKeys { propVars contains _ }).values.flatten
                    val Abs(_, ident, tpe, expr) = lambdaExpr(varProps): @unchecked
                    Abs(props ++ additonalProps, ident, tpe, expr)
                  (result, None, expr, typeVars, lambdaPropVars ++ propVars, external, customProperties)

                case _ =>
                  maybeFail[T](term.pos, recursive)
                  val (result, expr, typeVars, propVars, external) = processPropExpr(term, bound, externalTerms)
                  (result, None, expr, typeVars, propVars, external, List.empty)

      case _ =>
        Type.of[T] match
          case '[ Nothing ] =>
            maybeFail[T](term.pos, recursive)
            val (result, expr, typeVars, propVars, external) = processPropExpr(term, bound, externalTerms)
            (result, None, expr, typeVars, propVars, external, List.empty)

          case '[ p := (a, b) =>: r ] =>
            val names = bound map { _.name }
            val param0 = Naming.freshIdent("v", names)
            val param1 = Naming.freshIdent("v", names + param0)
            val etaExpandedTerm = Lambda(
              owner,
              MethodType(List(param0, param1))(_ => List(TypeRepr.of[a], TypeRepr.of[b]), _ => TypeRepr.of[r]),
              (_, args) =>
                val paramTerms = args map { case arg: Term => arg }
                Select.unique(term, "apply").appliedToArgs(paramTerms))

            val (result, _, expr, typeVars, propVars, external, customProperties) =
              processPropDef[T](etaExpandedTerm, owner, bound, externalTerms, recursiveSymbol, recursive = false)
            result match
              case Block(List(ClassDef(_, _, _, _, List(DefDef(_, _, _, Some(rhs))))), _) => rhs.changeOwner(owner).asExpr match
                case '{ ($result: (p := (a, b) =>: r)).apply($a, $b) } =>
                  (result.asTerm, None, expr, typeVars, propVars, external, customProperties)
                case _ =>
                  (result, None, expr, typeVars, propVars, external, customProperties)
              case _ =>
                (result, None, expr, typeVars, propVars, external, customProperties)

          case _ =>
            maybeFail[T](term.pos, recursive)
            val (result, expr, typeVars, propVars, external) = processPropExpr(term, bound, externalTerms)
            (result, None, expr, typeVars, propVars, external, List.empty)
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
              case PolyType(paramNames, paramBounds, _) if !isPropertyTypeBound(paramBounds(paramNum)) => paramNames(paramNum)
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

          case PolyType(paramNames, paramBounds, resType) if algebraicBaseType.isEmpty =>
            val (resTypes, resNames, resMake) = makeType(resType, types, None)
            val names = paramNames zip paramBounds collect { case (name, bound) if !isPropertyTypeBound(bound) => name }
            (resTypes,
             resNames -- names,
             variables => names.foldRight(resMake(variables)) { (param, res) => Universal(scala.Symbol(param), res) })

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

  def symbolTypeBounds(using Quotes)(symbol: quotes.reflect.Symbol) =
    import quotes.reflect.*
    TypeDef(symbol).rhs match
      case tree: TypeBoundsTree => Some(tree.tpe)
      case tree: TypeTree => tree.tpe match
        case bounds: TypeBounds => Some(bounds)
        case _ => None
      case _ => None

  def isPropertyTypeBound(using Quotes)(bounds: quotes.reflect.TypeBounds) =
    isProperty(bounds.hi) && isProperty(bounds.low)

  def propertiesTypeBound(using Quotes)(bounds: quotes.reflect.TypeBounds) =
    properties(bounds.hi)
    properties(bounds.low)

  def isProperty(using Quotes)(tpe: quotes.reflect.TypeRepr) =
    quotes.reflect.TypeRepr.of[Comm & Assoc & Idem & Sel & Refl & Irefl & Sym & Antisym & AntisymEq & Asym & Conn & Trans] <:< tpe

  def properties(using Quotes)(tpe: quotes.reflect.TypeRepr): (Properties, ListMap[quotes.reflect.Symbol, Properties]) =
    import quotes.reflect.*

    def fail(tpe: TypeRepr) = tpe.asType match
      case '[ t ] =>
        val hint =
          if tpe.typeSymbol.isTypeParam then
            val param = tpe match
              case TypeRef(NoPrefix(), name) => name
              case _ => "P"
            s"\nYou can specify polymorphic properties using a lower bound: $param >: (Prop1 & ... & PropN)"
          else
            ""
        report.errorAndAbort(s"Unknown property: ${printType[t]}$hint")

    def checkAndExtractPropVars(tpe: TypeRepr): ListMap[quotes.reflect.Symbol, Properties] =
      tpe.dealias match
        case tpe: AndType =>
          val leftPropVars = checkAndExtractPropVars(tpe.left)
          val rightPropVars = checkAndExtractPropVars(tpe.right)
          leftPropVars ++ rightPropVars
        case tpe: TypeRef if isProperty(tpe) =>
          val symbol = tpe.typeSymbol
          if symbol.isTypeParam then
            symbolTypeBounds(symbol) match
              case Some(bounds) =>
                val (props, propVars) = propertiesTypeBound(bounds)
                propVars + (symbol -> props)
              case _ =>
                fail(tpe)
          else
            ListMap.empty
        case _ =>
          fail(tpe)

    if !isProperty(tpe) then
      tpe.asType match
        case '[ t ] => report.errorAndAbort(s"Unknown property: ${printType[t]}")

    val properties = List(
      TypeRepr.of[Comm] -> Commutative,
      TypeRepr.of[Assoc] -> Associative,
      TypeRepr.of[Idem] -> Idempotent,
      TypeRepr.of[Sel] -> Selection,
      TypeRepr.of[Refl] -> Reflexive,
      TypeRepr.of[Irefl] -> Irreflexive,
      TypeRepr.of[Sym] -> Symmetric,
      TypeRepr.of[Antisym] -> Antisymmetric,
      TypeRepr.of[AntisymEq] -> AntisymmetricEq,
      TypeRepr.of[Asym] -> Asymmetric,
      TypeRepr.of[Conn] -> Connected,
      TypeRepr.of[Trans] -> Transitive)

    (properties collect {
      case (propertyType, property) if tpe <:< propertyType => property
    }).toSet -> checkAndExtractPropVars(tpe)
  end properties

  def property(using Quotes)(property: ast.Property): quotes.reflect.TypeRepr =
    import quotes.reflect.*
    property match
      case Commutative => TypeRepr.of[Comm]
      case Associative => TypeRepr.of[Assoc]
      case Idempotent => TypeRepr.of[Idem]
      case Selection => TypeRepr.of[Sel]
      case Reflexive => TypeRepr.of[Refl]
      case Irreflexive => TypeRepr.of[Irefl]
      case Symmetric => TypeRepr.of[Sym]
      case Antisymmetric => TypeRepr.of[Antisym]
      case AntisymmetricEq => TypeRepr.of[AntisymEq]
      case Asymmetric => TypeRepr.of[Asym]
      case Connected => TypeRepr.of[Conn]
      case Transitive => TypeRepr.of[Trans]

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
