package propel
package evaluator
package properties

import ast.*
import printing.*
import typer.*
import util.*

def check(expr: Term, printDebugInfo: Boolean = false): Term =
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

  def check(term: Term): Term = term match
    case Abs(properties, ident0, tpe0, expr0 @ Abs(_, ident1, tpe1, expr1)) =>
      if printDebugInfo && properties.nonEmpty then
        if debugInfoPrinted then
          println()
        else
          debugInfoPrinted = true
        println("Checking properties for definition:")
        println()
        println(indent(2, term.show))

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
              val converted = AlphaConversion.uniqueNames(expr).expr

              if printDebugInfo then
                println()
                println(indent(2, s"Checking ${property.show} property:"))
                println()
                println(indent(4, converted.show))

              val result = Symbolic.eval(converted, equalities)

              if printDebugInfo then
                println()
                println(indent(2, s"Evaluation result for ${property.show} property check:"))
                println()
                println(indent(4, result.show))

              val successful = checking.check(result)

              if printDebugInfo then
                println()
                if successful then
                  println(indent(4, s"✔ ${property.show} property proven".toUpperCase))
                else
                  println(indent(4, s"✘ ${property.show} property could not be proven".toUpperCase))

              Option.when(!successful)(propertyDeductionError(property))
      }
      error match
        case Some(error) => term.withExtrinsicInfo(error)
        case _ => Abs(term)(properties, ident0, tpe0, check(expr0))
    case Abs(properties, ident, tpe, expr) =>
      if properties.nonEmpty then
        term.withExtrinsicInfo(illshapedDefinitionError(properties.head))
      else
        Abs(term)(properties, ident, tpe, check(expr))
    case App(properties, expr, arg) =>
      App(term)(properties, check(expr), check(arg))
    case TypeAbs(ident, expr) =>
      TypeAbs(term)(ident, check(expr))
    case TypeApp(expr, tpe) =>
      TypeApp(term)(check(expr), tpe)
    case Data(ctor, args) =>
      Data(term)(ctor, args map check)
    case Var(_) =>
      expr
    case Cases(scrutinee, cases) =>
      Cases(term)(check(scrutinee), cases map { (pattern, expr) => pattern -> check(expr) })

  expr.typed match
    case expr -> Some(_) => check(expr)
    case expr -> _ => expr
end check
