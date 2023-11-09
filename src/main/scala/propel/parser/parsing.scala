package propel
package parser

import ast.*
import ast.dsl.*
import ast.dsl.sugar.*
import SExpr.*

import scala.util.{Failure, Success, Try}

def deserialize(string: String): Try[Term] =
  deserializeWithExpr(string, Data(Constructor(Symbol("Unit")), List.empty))

def deserializeWithExpr(string: String, exprToEval: Term): Try[Term] =
  def makeIdentifier(atom: Atom) =
    if atom.quote == Quote.None then
      atom.identifier match
        case "True" | "False" |
             "fun" | "forall" | "rec" |
             "lambda" | "let" | "letrec" | "lettype" | "if" | "not" | "or" | "and" | "implies" | "cases" |
             "def" | "type" =>
          throw ParserException(s"Invalid identifier: ${atom.identifier}")
        case _ =>
    Symbol(atom.identifier)

  def makeConstructor(atom: Atom) =
    if atom.quote == Quote.None && atom.identifier == "True" then
      Some(Constructor.True)
    else if atom.quote == Quote.None && atom.identifier == "False" then
      Some(Constructor.False)
    else if atom.quote == Quote.Single || atom.quote == Quote.None && (atom.identifier.headOption exists { _.isUpper }) then
      Some(Constructor(makeIdentifier(atom)))
    else
      None

  def deserializeProperty(expr: SExpr): Property = expr match
    case Atom("comm", Quote.None) => Commutative
    case Atom("assoc", Quote.None) => Associative
    case Atom("idem", Quote.None) => Idempotent
    case Atom("sel", Quote.None) => Selection
    case Atom("refl", Quote.None) => Reflexive
    case Atom("irefl", Quote.None) => Irreflexive
    case Atom("sym", Quote.None) => Symmetric
    case Atom("antisym", Quote.None) => Antisymmetric
    case Atom("antisym-eq", Quote.None) => AntisymmetricEq
    case Atom("asym", Quote.None) => Asymmetric
    case Atom("conn", Quote.None) => Connected
    case Atom("trans", Quote.None) => Transitive
    case _ => throw ParserException("Invalid property")

  def deserializeProperties(expr: List[SExpr]): Properties =
    (expr map deserializeProperty).toSet

  def deserializeType(expr: SExpr): Type = expr match
    case expr @ (Atom(_, Quote.Single | Quote.Single) | Atom("True" | "False", _)) =>
      makeConstructor(expr).fold(TypeVar(makeIdentifier(expr))) { ctor => Sum(List(ctor -> List.empty)) }
    case expr @ Atom(_, _) =>
      TypeVar(makeIdentifier(expr))
    case Expr(_, Bracket.Square) =>
      throw ParserException("Invalid use of square bracket")
    case Expr(Atom("fun", Quote.None) :: exprs, Bracket.Paren) =>
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid function type")
      exprs.init.foldRight(deserializeType(exprs.last)) { (expr, tpe) => Function(deserializeType(expr), tpe) }
    case Expr(Atom("forall", Quote.None) :: exprs, Bracket.Paren) =>
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid universal type")
      exprs.init.foldRight(deserializeType(exprs.last)) {
        case (expr @ Atom(_, _), tpe) => Universal(makeIdentifier(expr), tpe)
        case _ => throw ParserException("Invalid universal type")
      }
    case Expr(Atom("rec", Quote.None) :: exprs, Bracket.Paren) =>
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid recursive type")
      exprs.init.foldRight(deserializeType(exprs.last)) {
        case (expr @ Atom(_, _), tpe) => Recursive(makeIdentifier(expr), tpe)
        case _ => throw ParserException("Invalid recursive type")
      }
    case Expr(List(atom @ Atom(_, _)), Bracket.Paren) =>
      Sum(List(Constructor(makeIdentifier(atom)) -> List.empty))
    case Expr(List(expr), Bracket.Paren) =>
      deserializeType(expr)
    case Expr(exprs, Bracket.Paren | Bracket.Brace) =>
      Sum(exprs map {
        case expr @ Atom(_, _) =>
          (makeConstructor(expr) getOrElse Constructor(makeIdentifier(expr))) -> List.empty
        case Expr((expr @ Atom(_, _)) :: exprs, Bracket.Paren) =>
          Constructor(makeIdentifier(expr)) -> (exprs map deserializeType)
        case _ =>
          throw ParserException("Invalid sum type")
      })

  def deserializePattern(expr: SExpr): Pattern = expr match
    case expr @ Atom(identifier, quote) =>
      makeConstructor(expr).fold(Bind(makeIdentifier(expr))) { Match(_, List.empty) }
    case Expr(_, Bracket.Brace) =>
      throw ParserException("Invalid use of brace")
    case Expr(_, Bracket.Square) =>
      throw ParserException("Invalid use of square bracket")
    case Expr(List(expr), Bracket.Paren) =>
      deserializePattern(expr)
    case Expr((expr @ Atom(_, _)) :: exprs, Bracket.Paren) =>
      Match(Constructor(makeIdentifier(expr)), exprs map deserializePattern)
    case Expr(_, Bracket.Paren) =>
      throw ParserException("Invalid pattern")

  def deserializeTerm(expr: SExpr): Term = expr match
    case expr @ Atom(identifier, quote) =>
      makeConstructor(expr).fold(Var(makeIdentifier(expr))) { Data(_, List.empty) }
    case Expr(_, Bracket.Brace) =>
      throw ParserException("Invalid use of brace")
    case Expr(_, Bracket.Square) =>
      throw ParserException("Invalid use of square bracket")
    case Expr(Atom("let", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(pattern, bound, expr) => let(deserializePattern(pattern) -> deserializeTerm(bound))(deserializeTerm(expr))
        case _ => throw ParserException("Invalid let binding")
    case Expr(Atom("letrec", Quote.None) :: exprs, Bracket.Paren) =>
      given BindingExpr[List[SExpr]] = _ map {
        case Expr(List(expr @ Atom(_, _), tpe, bound), Bracket.Paren | Bracket.Square) =>
          (makeIdentifier(expr), deserializeType(tpe), deserializeTerm(bound))
        case _ =>
          throw ParserException("Invalid letrec binding")
      }
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid letrec binding")
      exprs match
        case List(expr @ Atom(_, _), tpe, bound, body) => letrec(List(Expr(List(expr, tpe, bound), Bracket.Paren)))(deserializeTerm(body))
        case _ => letrec(exprs.init)(deserializeTerm(exprs.last))
    case Expr(Atom("lettype", Quote.None) :: exprs, Bracket.Paren) =>
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid lettype definition")
      val types = exprs match
        case List(Atom(arg, _), tpe, _) => List(arg -> deserializeType(tpe))
        case _ => exprs.init map {
          case Expr(List(Atom(arg, _), tpe), Bracket.Paren | Bracket.Square) => arg -> deserializeType(tpe)
          case _ => throw ParserException("Invalid lettype definition")
        }
      lettype(types.head, types.tail*)(deserializeTerm(exprs.last))
    case Expr(Atom("if", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(condExpr, thenExpr, elseExpr) => `if`(deserializeTerm(condExpr))(deserializeTerm(thenExpr))(deserializeTerm(elseExpr))
        case _ => throw ParserException("Invalid if condition")
    case Expr(Atom("not", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(expr) => not(deserializeTerm(expr))
        case _ => throw ParserException("Invalid not operator")
    case Expr(Atom("or", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(rhsExpr, lhsExpr) => or(deserializeTerm(rhsExpr))(deserializeTerm(lhsExpr))
        case _ => throw ParserException("Invalid or operator")
    case Expr(Atom("and", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(rhsExpr, lhsExpr) => and(deserializeTerm(rhsExpr))(deserializeTerm(lhsExpr))
        case _ => throw ParserException("Invalid and operator")
    case Expr(Atom("implies", Quote.None) :: exprs, Bracket.Paren) =>
      exprs match
        case List(rhsExpr, lhsExpr) => implies(deserializeTerm(rhsExpr))(deserializeTerm(lhsExpr))
        case _ => throw ParserException("Invalid implies operator")
    case Expr(Atom("cases", Quote.None) :: exprs, Bracket.Paren) =>
      if exprs.sizeIs < 2 then
        throw ParserException("Invalid pattern match")
      val scrutinee = deserializeTerm(exprs.head)
      val cases = exprs.tail map {
        case Expr(List(pattern, expr), Bracket.Paren | Bracket.Square) => deserializePattern(pattern) -> deserializeTerm(expr)
        case _ => throw ParserException("Invalid pattern match")
      }
      Cases(scrutinee, cases)
    case Expr(Atom("lambda", Quote.None) :: exprs, Bracket.Paren) =>
      val body = deserializeTerm(exprs.last)
      exprs.init.foldRight(body) {
        case (Expr(properties, Bracket.Square), expr @ Abs(_, _, _, _)) if expr ne body =>
          Abs(deserializeProperties(properties), expr.ident, expr.tpe, expr.expr)
        case (Expr(List(Atom(arg, _), tpe), Bracket.Paren), expr) =>
          Abs(Set.empty, Symbol(arg), deserializeType(tpe), expr)
        case (Atom(arg, _), expr) =>
          TypeAbs(Symbol(arg), expr)
        case _ =>
          throw ParserException("Invalid lambda definition")
      }
    case Expr(expr, Bracket.Paren) =>
      val (properties, exprs) = expr match
        case Expr(properties, Bracket.Square) :: exprs => (deserializeProperties(properties), exprs)
        case exprs => (Set.empty, exprs)
      if exprs.isEmpty then
        throw ParserException("Invalid empty expression")
      (exprs.head, deserializeTerm(exprs.head)) match
        case (Atom(_, _), Data(ctor, List())) if (exprs eq expr) =>
          Data(ctor, exprs.tail map deserializeTerm)
        case (_, expr) =>
          exprs.tail.foldLeft(expr) {
            case (term, Expr(args, Bracket.Square)) =>
              if args.isEmpty then
                throw ParserException("Invalid empty expression")
              args.foldLeft(term) { (expr, arg) => TypeApp(expr, deserializeType(arg)) }
            case (term, arg) =>
              val props = if term eq expr then properties else Set.empty
              App(props, term, deserializeTerm(arg))
          }

  SExpr.deserialize(string) map { exprs =>
    if exprs.isEmpty then
      throw ParserException("Input empty")

    val (term, _) = exprs.foldRight[(Term, Boolean)](exprToEval -> true) {
      case (Expr(Atom("type", Quote.None) :: exprs, Bracket.Paren), term -> _) =>
        exprs match
          case List(Atom(arg, _), tpe) =>
            lettype(arg -> deserializeType(tpe))(term) -> false
          case _ =>
            throw ParserException("Invalid type definition")
      case (Expr(Atom("def", Quote.None) :: exprs, Bracket.Paren), term -> _) =>
        exprs match
          case List(Atom(arg, _), expr) =>
            let(arg -> deserializeTerm(expr))(term) -> false
          case List(Atom(arg, _), tpe, expr) =>
            letrec(arg -> deserializeType(tpe) -> deserializeTerm(expr))(term) -> false
          case _ =>
            throw ParserException("Invalid term definition")
      case (expr, term -> last) =>
        if last then
          deserializeTerm(expr) -> false
        else
          val intermediateTerm = deserializeTerm(expr)
          val free = (intermediateTerm.syntacticInfo.freeVars map { (ident, _) => ident.name }).toSet
          val wildcardName = Naming.freshIdent("_", free)
          let(wildcardName -> intermediateTerm)(term) -> false
    }

    term
  }
end deserializeWithExpr

def serialize(term: Term): String =
  def makeIdentifier(ident: Symbol, noUpperCase: Boolean) = ident.name match
    case "True" | "False" |
         "fun" | "forall" | "rec" |
         "lambda" | "let" | "letrec" | "lettype" | "if" | "not" | "or" | "and" | "implies" | "cases" |
         "def" | "type" =>
      Atom(ident.name, Quote.Double)
    case name =>
      if noUpperCase && (name.headOption exists { _.isUpper }) || SExpr.requiresQuotes(name) then
        Atom(ident.name, Quote.Double)
      else
        Atom(ident.name, Quote.None)

  def makeTypeIdentifier(ident: Symbol) = makeIdentifier(ident, noUpperCase = false)

  def makeTermIdentifier(ident: Symbol) = makeIdentifier(ident, noUpperCase = true)

  def makeConstructorIdentifier(ctor: Constructor) = ctor match
    case Constructor.True => Atom("True", Quote.None)
    case Constructor.False => Atom("False", Quote.None)
    case Constructor(ident) =>
      if (ident.name.headOption exists { _.isUpper }) && !SExpr.requiresQuotes(ident.name) then
        Atom(ident.name, Quote.None)
      else
        Atom(ident.name, Quote.Single)

  val propertyExprs = List(
    Commutative -> Atom("comm", Quote.None),
    Associative -> Atom("assoc", Quote.None),
    Idempotent -> Atom("idem", Quote.None),
    Selection -> Atom("sel", Quote.None),
    Reflexive -> Atom("refl", Quote.None),
    Irreflexive -> Atom("irefl", Quote.None),
    Symmetric -> Atom("sym", Quote.None),
    Antisymmetric -> Atom("antisym", Quote.None),
    Asymmetric -> Atom("asym", Quote.None),
    Connected -> Atom("conn", Quote.None),
    Transitive -> Atom("trans", Quote.None))

  def serializeProperties(properties: Properties): Option[SExpr] =
    val result = propertyExprs.foldRight(List.empty[SExpr]) { case ((property, expr), result) =>
      if properties contains property then expr :: result else result
    }
    Option.when(result.nonEmpty) { Expr(result, Bracket.Square) }

  def collapseTypeDefinitions(definition: String, tpe: Type) = serializeType(tpe) match
    case Expr(Atom(`definition`, Quote.None) :: exprs, Bracket.Paren) =>
      exprs
    case expr =>
      List(expr)

  def serializeType(tpe: Type): SExpr = tpe match
    case Function(arg, result) =>
      Expr(Atom("fun", Quote.None) :: serializeType(arg) :: collapseTypeDefinitions("fun", result), Bracket.Paren)
    case Universal(ident, result) =>
      Expr(Atom("forall", Quote.None) :: makeTypeIdentifier(ident) :: collapseTypeDefinitions("forall", result), Bracket.Paren)
    case Recursive(ident, result) =>
      Expr(Atom("rec", Quote.None) :: makeTypeIdentifier(ident) :: collapseTypeDefinitions("rec", result), Bracket.Paren)
    case TypeVar(ident) =>
      makeTypeIdentifier(ident)
    case Sum(sum) =>
      val result = sum map { (ctor, args) =>
        val expr = makeConstructorIdentifier(ctor)
        if args.isEmpty then expr else Expr(expr :: (args map serializeType), Bracket.Paren)
      }
      Expr(result, Bracket.Brace)

  def serializePattern(pattern: Pattern): SExpr = pattern match
    case Match(ctor, args) =>
      if args.isEmpty then
        makeConstructorIdentifier(ctor)
      else
        Expr(makeConstructorIdentifier(ctor) :: (args map serializePattern), Bracket.Paren)
    case Bind(ident) =>
      makeTermIdentifier(ident)

  def collapseLambdas(prefix: List[SExpr], expr: SExpr) = expr match
    case expr @ Expr(Atom("lambda", Quote.None) :: Expr(_, Bracket.Square) :: _, Bracket.Paren) =>
      Expr(prefix :+ expr, Bracket.Paren)
    case Expr(Atom("lambda", Quote.None) :: exprs, Bracket.Paren) =>
      Expr(prefix ++ exprs, Bracket.Paren)
    case expr =>
      Expr(prefix :+ expr, Bracket.Paren)

  def serializeTerm(term: Term): SExpr = term match
    case Abs(properties, ident, tpe, expr) =>
      val arg = Expr(List(makeTermIdentifier(ident), serializeType(tpe)), Bracket.Paren)
      val props = serializeProperties(properties)
      collapseLambdas((List(Atom("lambda", Quote.None)) ++ props) :+ arg, serializeTerm(expr))
    case App(properties, expr, arg) =>
      val props = serializeProperties(properties)
      (expr, serializeTerm(expr)) match
        case (App(_, _, _) | TypeApp(_, _), Expr(exprs, Bracket.Paren)) if props.isEmpty =>
          Expr(exprs :+ serializeTerm(arg), Bracket.Paren)
        case (_, expr) =>
          Expr(props.toList :+ expr :+ serializeTerm(arg), Bracket.Paren)
    case TypeAbs(ident, expr) =>
      collapseLambdas(List(Atom("lambda", Quote.None), makeTypeIdentifier(ident)), serializeTerm(expr))
    case TypeApp(expr, tpe) =>
      (expr, serializeTerm(expr)) match
        case (App(_, _, _), Expr(exprs, Bracket.Paren)) =>
          Expr(exprs :+ Expr(List(serializeType(tpe)), Bracket.Square), Bracket.Paren)
        case (TypeApp(_, _), Expr(exprs :+ Expr(tpes, Bracket.Square), Bracket.Paren)) =>
          Expr(exprs :+ Expr(tpes :+ serializeType(tpe), Bracket.Square), Bracket.Paren)
        case (_, expr) =>
          Expr(List(expr, Expr(List(serializeType(tpe)), Bracket.Square)), Bracket.Paren)
    case Data(ctor, List()) =>
      makeConstructorIdentifier(ctor)
    case Data(ctor, args) =>
      Expr(makeConstructorIdentifier(ctor) :: (args map serializeTerm), Bracket.Paren)
    case Var(ident) =>
      makeTermIdentifier(ident)
    case Cases(bound, List(pattern -> expr)) =>
      Expr(List(Atom("let", Quote.None), serializePattern(pattern), serializeTerm(bound), serializeTerm(expr)), Bracket.Paren)
    case Cases(expr, List(Match(Constructor.True, List()) -> Data(Constructor.False, List()), Match(Constructor.False, List()) -> Data(Constructor.True, List()))) =>
      Expr(List(Atom("not", Quote.None), serializeTerm(expr)), Bracket.Paren)
    case Cases(lhsExpr, List(Match(Constructor.True, List()) -> Data(Constructor.True, List()), Match(Constructor.False, List()) -> rhsExpr)) =>
      Expr(List(Atom("or", Quote.None), serializeTerm(lhsExpr), serializeTerm(rhsExpr)), Bracket.Paren)
    case Cases(lhsExpr, List(Match(Constructor.True, List()) -> rhsExpr, Match(Constructor.False, List()) -> Data(Constructor.False, List()))) =>
      Expr(List(Atom("and", Quote.None), serializeTerm(lhsExpr), serializeTerm(rhsExpr)), Bracket.Paren)
    case Cases(lhsExpr, List(Match(Constructor.True, List()) -> rhsExpr, Match(Constructor.False, List()) -> Data(Constructor.True, List()))) =>
      Expr(List(Atom("implies", Quote.None), serializeTerm(lhsExpr), serializeTerm(rhsExpr)), Bracket.Paren)
    case Cases(condExpr, List(Match(Constructor.True, List()) -> thenExpr, Match(Constructor.False, List()) -> elseExpr)) =>
      Expr(List(Atom("if", Quote.None), serializeTerm(condExpr), serializeTerm(thenExpr), serializeTerm(elseExpr)), Bracket.Paren)
    case Cases(scrutinee, cases) =>
      val exprs = cases map { (pattern, expr) =>
        Expr(List(serializePattern(pattern), serializeTerm(expr)), Bracket.Square)
      }
      Expr(Atom("cases", Quote.None) :: serializeTerm(scrutinee) :: exprs, Bracket.Paren)

  SExpr.serialize(serializeTerm(term))
end serialize
