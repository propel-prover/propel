package propel
package dsl.impl

import ast.*
import evaluator.properties.Normalization

import scala.quoted.{Type => _, *}


given SymbolToExpr: ToExpr[Symbol] with
  def apply(symbol: Symbol)(using Quotes) =
    '{ Symbol(${Expr(symbol.name)}) }

given PropertyToExpr: ToExpr[Property] with
  def apply(property: Property)(using Quotes) = property match
    case Commutative => '{ Commutative }
    case Associative => '{ Associative }
    case Idempotent => '{ Idempotent }
    case Selection => '{ Selection }
    case Reflexive => '{ Reflexive }
    case Irreflexive => '{ Irreflexive }
    case Symmetric => '{ Symmetric }
    case Antisymmetric => '{ Antisymmetric }
    case AntisymmetricEq => '{ AntisymmetricEq }
    case Asymmetric => '{ Asymmetric }
    case Connected => '{ Connected }
    case Transitive => '{ Transitive }

given ConstructorToExpr: ToExpr[Constructor] with
  def apply(ctor: Constructor)(using Quotes) =
    '{ Constructor(${Expr(ctor.ident)}) }

given PatternToExpr: ToExpr[Pattern] with
  def apply(pattern: Pattern)(using Quotes) = pattern match
    case Match(ctor, args) => '{ Match(${Expr(ctor)}, ${Expr(args)}) }
    case Bind(ident) => '{ Bind(${Expr(ident)}) }

given TypeToExpr: ToExpr[Type] with
  def apply(tpe: Type)(using Quotes) = tpe match
    case Function(arg, result) => '{ Function(${Expr(arg)}, ${Expr(result)}) }
    case Universal(ident, result) => '{ Universal(${Expr(ident)}, ${Expr(result)}) }
    case Recursive(ident, result) => '{ Recursive(${Expr(ident)}, ${Expr(result)}) }
    case TypeVar(ident) => '{ TypeVar(${Expr(ident)}) }
    case Sum(sum) => '{ Sum(${Expr(sum)}) }

given TermToExpr: ToExpr[Term] with
  def apply(term: Term)(using Quotes) = term match
    case Abs(properties, ident, tpe, expr) => '{ Abs(${Expr(properties)}, ${Expr(ident)}, ${Expr(tpe)}, ${Expr(expr)}) }
    case App(properties, expr, arg) => '{ App(${Expr(properties)}, ${Expr(expr)}, ${Expr(arg)}) }
    case TypeAbs(ident, expr) => '{ TypeAbs(${Expr(ident)}, ${Expr(expr)}) }
    case TypeApp(expr, tpe) => '{ TypeApp(${Expr(expr)}, ${Expr(tpe)}) }
    case Data(ctor, args) => '{ Data(${Expr(ctor)}, ${Expr(args)}) }
    case Var(ident) => '{ Var(${Expr(ident)}) }
    case Cases(scrutinee, cases) => '{ Cases(${Expr(scrutinee)}, ${Expr(cases)}) }

given NormalizationToExpr: ToExpr[Normalization] with
  def apply(normalization: Normalization)(using Quotes) =
    val Normalization(pattern, result, abstraction, variables, reversible) = normalization
    '{ Normalization(${Expr(pattern)}, ${Expr(result)}, ${Expr(abstraction)}, ${Expr(variables)}, ${Expr(reversible)}) }


given SymbolFromExpr: FromExpr[Symbol] with
  def unapply(symbol: Expr[Symbol])(using Quotes) = symbol match
    case '{ Symbol(${Expr(name)}) } => Some(Symbol(name))
    case _ => None

given PropertyFromExpr: FromExpr[Property] with
  def unapply(property: Expr[Property])(using Quotes) = property match
    case '{ Commutative } => Some(Commutative)
    case '{ Associative } => Some(Associative)
    case '{ Idempotent } => Some(Idempotent)
    case '{ Selection } => Some(Selection)
    case '{ Reflexive } => Some(Reflexive)
    case '{ Irreflexive } => Some(Irreflexive)
    case '{ Symmetric } => Some(Symmetric)
    case '{ Antisymmetric } => Some(Antisymmetric)
    case '{ Asymmetric } => Some(Asymmetric)
    case '{ Connected } => Some(Connected)
    case '{ Transitive } => Some(Transitive)
    case _ => None

given ConstructorFromExpr: FromExpr[Constructor] with
  def unapply(ctor: Expr[Constructor])(using Quotes) = ctor match
    case '{ Constructor(${Expr(ident)}) } => Some(Constructor(ident))
    case '{ new Constructor(${Expr(ident)}) } => Some(Constructor(ident))
    case _ => None

given PatternFromExpr: FromExpr[Pattern] with
  def unapply(pattern: Expr[Pattern])(using Quotes) = pattern match
    case '{ Match(${Expr(ctor)}, ${Expr(args)}) } => Some(Match(ctor, args))
    case '{ Bind(${Expr(ident)}: Symbol) } => Some(Bind(ident))
    case _ => None

given TypeFromExpr: FromExpr[Type] with
  def unapply(tpe: Expr[Type])(using Quotes) = tpe match
    case '{ Function(${Expr(arg)}, ${Expr(result)}) } => Some(Function(arg, result))
    case '{ Universal(${Expr(ident)}, ${Expr(result)}) } => Some(Universal(ident, result))
    case '{ Recursive(${Expr(ident)}, ${Expr(result)}) } => Some(Recursive(ident, result))
    case '{ TypeVar(${Expr(ident)}: Symbol) } => Some(TypeVar(ident))
    case '{ Sum(${Expr(sum)}: List[(Constructor, List[Type])]) } => Some(Sum(sum))
    case _ => None

given TermFromExpr: FromExpr[Term] with
  def unapply(term: Expr[Term])(using Quotes) = term match
    case '{ Abs(${Expr(properties)}, ${Expr(ident)}, ${Expr(tpe)}, ${Expr(expr)}) } => Some(Abs(properties, ident, tpe, expr))
    case '{ App(${Expr(properties)}, ${Expr(expr)}, ${Expr(arg)}) } => Some(App(properties, expr, arg))
    case '{ TypeAbs(${Expr(ident)}, ${Expr(expr)}) } => Some(TypeAbs(ident, expr))
    case '{ TypeApp(${Expr(expr)}, ${Expr(tpe)}) } => Some(TypeApp(expr, tpe))
    case '{ Data(${Expr(ctor)}, ${Expr(args)}) } => Some(Data(ctor, args))
    case '{ Var(${Expr(ident)}: Symbol) } => Some(Var(ident))
    case '{ Cases(${Expr(scrutinee)}: Term, ${Expr(cases)}: List[(Pattern, Term)]) } => Some(Cases(scrutinee, cases))
    case _ => None

given NormalizationFromExpr: FromExpr[Normalization] with
  def unapply(normalization: Expr[Normalization])(using Quotes) = normalization match
    case '{ Normalization(${Expr(pattern)}, ${Expr(result)}, ${Expr(abstraction)}, ${Expr(variables)}, ${Expr(reversible)}) } =>
      Some(Normalization(pattern, result, abstraction, variables, reversible))
    case _ =>
      None
