package propel
package evaluator
package properties

import ast.*
import typer.*
import printing.*
import util.*

case class CustomProperties(normalizations: List[Normalization]) extends Enrichment(CustomProperties)

object CustomProperties extends Enrichment.Extrinsic[Term, CustomProperties]

def addCustomProperty(term: Term, abstraction: Abstraction, normalization: Normalization): Term =
  var customPropertyAdded = false

  def addToDefinition(term: Term): Term = term match
    case Abs(properties, ident, tpe, expr @ Abs(_, _, _, _)) if term.info(Abstraction) contains abstraction =>
      customPropertyAdded = true
      val normalizations = term.info(CustomProperties).fold(List.empty) { _.normalizations }
      Abs(term)(properties, ident, tpe, addToDefinition(expr)).withExtrinsicInfo(CustomProperties(normalizations :+ normalization))
    case Abs(properties, ident, tpe, expr) => Abs(term)(properties, ident, tpe, addToDefinition(expr))
    case App(properties, expr, arg) => App(term)(properties, addToDefinition(expr), addToDefinition(arg))
    case TypeAbs(ident, expr) => TypeAbs(term)(ident, addToDefinition(expr))
    case TypeApp(expr, tpe) => TypeApp(term)(addToDefinition(expr), tpe)
    case Data(ctor, args) => Data(term)(ctor, args map addToDefinition)
    case Var(_) => term
    case Cases(scrutinee, cases) => Cases(term)(addToDefinition(scrutinee), cases map { (pattern, expr) =>
      pattern -> addToDefinition(expr)
    })

  val expr = addToDefinition(term)
  if !customPropertyAdded then
    throw throw new RuntimeException(s"[Implementation restriction] Function requires two arguments: ${normalization.abstraction.name}")
  expr
end addCustomProperty

def addCustomProperty(pattern: Term, result: Term, variables: Set[Symbol], abstraction: Symbol, expr: Term): Term =
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

  val normalization = Normalization(pattern, result, abstraction, variables, reversible = true)
  val typedExpr = expr.typedTerm
  addCustomProperty(typedExpr, abstractionByName(typedExpr, abstraction), normalization)
end addCustomProperty

def interpretAndAddAllCustomProperties(term: Term): Term =
  def collectVariables(term: Term): (Set[Symbol], Term) = term match
    case Abs(_, ident, _, expr) => let(collectVariables(expr)) { (variables, expr) => variables + ident -> expr }
    case _ => Set.empty -> term

  def collectCustomProperties(term: Term): List[(Abstraction, Normalization)] = term match
    case Abs(_, _, _, expr) => collectCustomProperties(expr)
    case App(_, App(_, Var(Symbol("prop-for")), abstraction @ Var(ident)), property) =>
      if term.info(CustomProperties).isDefined then
        if abstraction.info(Abstraction).isEmpty then
          throw throw new RuntimeException(s"Properties can only be specified for functions: ${ident.name}")

        collectVariables(property) match
          case (variables, term @ App(_, App(_, Var(Symbol("==")), pattern), result)) if term.info(CustomProperties).isDefined =>
            if !(pattern.syntacticInfo.freeVars contains ident) && !(result.syntacticInfo.freeVars contains ident) then
              throw throw new RuntimeException(s"The function ${ident.name} needs to appear in the property: ${term.show}")

            List(abstraction.info(Abstraction).get -> Normalization(pattern, result, ident, variables, reversible = true))

          case _ =>
            List.empty
      else
        List.empty
    case App(_, expr, arg) => collectCustomProperties(expr) ++ collectCustomProperties(arg)
    case TypeAbs(_, expr) => collectCustomProperties(expr)
    case TypeApp(expr, _) => collectCustomProperties(expr)
    case Data(_, args) => args flatMap collectCustomProperties
    case Var(_) => List.empty
    case Cases(scrutinee, cases) => collectCustomProperties(scrutinee) ++ (cases flatMap { (_, expr) => collectCustomProperties(expr) })

  collectCustomProperties(term).foldLeft(term) { case (term, (abstraction, normalization)) =>
    addCustomProperty(term, abstraction, normalization)
  }
end interpretAndAddAllCustomProperties
