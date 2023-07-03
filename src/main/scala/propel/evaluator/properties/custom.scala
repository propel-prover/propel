package propel
package evaluator
package properties

import ast.*
import typer.*

case class CustomProperties(normalizations: List[Normalization]) extends Enrichment(CustomProperties)

object CustomProperties extends Enrichment.Extrinsic[Term, CustomProperties]

def addCustomProperty(pattern: Term, result: Term, variables: Set[Symbol], abstraction: Symbol, expr: Term) =
  def patternAbstractions(pattern: Pattern): List[(Symbol, Abstraction)] = pattern match
    case Match(_, args) => args flatMap patternAbstractions
    case Bind(ident) => (pattern.patternType flatMap { _.info(Abstraction) }).fold(List.empty) { abstraction =>
      List(ident -> abstraction)
    }

  def termAbstractions(expr: Term): List[(Symbol, Abstraction)] = expr match
    case Abs(_, _, _, expr) => termAbstractions(expr)
    case App(_, expr, arg) => termAbstractions(expr) ++ termAbstractions(arg)
    case TypeAbs(_, expr) => termAbstractions(expr)
    case TypeApp(expr, _) => termAbstractions(expr)
    case Data(_, args) => args flatMap termAbstractions
    case Var(_) => List.empty
    case Cases(scrutinee, cases) => termAbstractions(scrutinee) ++ (cases flatMap { (pattern, expr) =>
      patternAbstractions(pattern) ++ termAbstractions(expr)
    })

  def abstractionByName(expr: Term, ident: Symbol) =
    (termAbstractions(expr) collect { case (`ident`, abstraction) => abstraction }).distinct match
      case List(abstraction) => abstraction
      case List() => throw new RuntimeException(s"Identifier not found: ${ident.name}")
      case _ => throw new RuntimeException(s"Identifier ambiguous: ${ident.name}")

  def addToDefinition(expr: Term, abstraction: Abstraction, name: String, normalization: Normalization) =
    def addToDefinition(term: Term): Term = term match
      case Abs(properties, ident, tpe, expr @ Abs(_, _, _, _)) if term.info(Abstraction) contains abstraction =>
        val normalizations = term.info(CustomProperties).fold(List.empty) { _.normalizations }
        Abs(term)(properties, ident, tpe, addToDefinition(expr)).withExtrinsicInfo(CustomProperties(normalizations :+ normalization))
      case Abs(_, _, _, _) if term.info(Abstraction) contains abstraction =>
        throw throw new RuntimeException(s"[Implementation restriction] Function requires two arguments: $name")
      case Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe, addToDefinition(expr))
      case App(properties, expr, arg) => App(term)(properties, addToDefinition(expr), addToDefinition(arg))
      case TypeAbs(ident, expr) => TypeAbs(term)(ident, addToDefinition(expr))
      case TypeApp(expr, tpe) => TypeApp(term)(addToDefinition(expr), tpe)
      case Data(ctor, args) => Data(term)(ctor, args map addToDefinition)
      case Var(_) => term
      case Cases(scrutinee, cases) => Cases(term)(addToDefinition(scrutinee), cases map { (pattern, expr) =>
        pattern -> addToDefinition(expr)
      })
    addToDefinition(expr)

  val normalization = Normalization(pattern, result, abstraction, variables, reversible = true)
  val typedExpr = expr.typedTerm
  addToDefinition(typedExpr, abstractionByName(typedExpr, abstraction), abstraction.name, normalization)
end addCustomProperty
