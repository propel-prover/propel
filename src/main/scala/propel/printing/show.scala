package propel
package printing

import impl.*
import ast.*

extension (property: Property) def show: String = property match
  case Commutative => "comm"
  case Associative => "assoc"
  case Idempotent => "idem"
  case Reflexive => "refl"
  case Irreflexive => "irefl"
  case Symmetric => "sym"
  case Antisymmetric => "antisym"
  case Asymmetric => "asym"
  case Connected => "conn"
  case Transitive => "trans"

extension (properties: Properties) def show: String = properties.map(_.show).mkString(", ")

extension (constructor: Constructor) def show: String = constructor.ident.name

extension (tpe: Type) def show: String = tpe.format.asString

extension (pattern: Pattern) def show: String = pattern.format.asString

extension (expr: Term) def show: String = expr.format.asString

extension (error: (Type | Pattern | Term, Error)) def show: String = error.show(null)

extension (error: (Type | Pattern | Term, Error)) def show(tree: Type | Pattern | Term | Null): String =
  val (construct, Error(message)) = error

  val format = ((if tree != null then tree else construct): Type | Pattern | Term) match
    case construct: Type => List(construct.format)
    case construct: Pattern => List(construct.format)
    case construct: Term => construct.format

  val output =
    format.range(construct) map { case ((startLine, startColumn), (endLine, endColumn)) =>
      val line = format(startLine).asString
      val length = if endLine > startLine then line.length - startColumn else endColumn - startColumn
      val marker = " " * startColumn + "^" * length
      s"$line\n$marker\n$message"
    } getOrElse message

  val indicator = "[error] "

  s"$indicator${output.replaceAll("\r\n|\r|\n", s"${System.lineSeparator}$indicator")}"

extension (construct: Type | Pattern | Term) def showErrors: String =
  (construct.errors map { _.show(construct) }).mkString(s"${System.lineSeparator}${System.lineSeparator}")

extension (result: evaluator.Symbolic.Result) def show: String =
  def parenthesize(value: Term | Pattern) = value match
    case value @ (Bind(_) | Match(_, List())) => value.show
    case value @ (Var(_) | Data(_, List())) => value.show
    case value: Term => s"(${value.show})"
    case value: Pattern => s"(${value.show})"

  (result.reductions map { case evaluator.Symbolic.Reduction(expr, constraints, equalities) =>
    "• " + expr.show + "\n  Pattern Constraints\n" +
    (constraints.pos map { (expr, pattern) =>
      parenthesize(expr) + "≔" + parenthesize(pattern)
    }).toList.sorted.mkString("   pos: {", ", ", "}\n") +
    (constraints.neg map { neg =>
      (neg map { (expr, pattern) => parenthesize(expr) + "≔" + parenthesize(pattern) }).toList.sorted.mkString("{", ", ", "}")
    }).toList.sorted.mkString("   neg: {", ", ", "}\n  Equalities\n") +
    (equalities.pos map { (expr0, expr1) =>
      parenthesize(expr0) + "≡" + parenthesize(expr1)
    }).toList.sorted.mkString("   pos: {", ", ", "}\n") +
    (equalities.neg map { neg =>
      (neg map { (expr0, expr1) => parenthesize(expr0) + "≡" + parenthesize(expr1) }).toList.sorted.mkString("{", ", ", "}")
    }).toList.sorted.mkString("   neg: {", ", ", "}")
  }).mkString("\n\n")

extension (normalization: evaluator.properties.Normalization) def show: String =
  val functionForm = if normalization.form.isEmpty then "" else s" of form ${normalization.form.get.show}"
  val variables =
    normalization.pattern.syntacticInfo.freeVars.keySet ++
    normalization.result.syntacticInfo.freeVars.keySet --
    normalization.idents

  val functionNames =
    if normalization.idents.isEmpty then ""
    else s" for function ${(normalization.idents.toList.sorted map { _.name }).mkString(", ")}$functionForm"

  val variableNames =
    val prefix = if functionNames.isEmpty then "for" else "and"
    if variables.isEmpty then ""
    else s" $prefix variables ${(variables.toList.sorted map { _.name }).mkString(", ")}"

  s"${normalization.pattern.show} ⥱ ${normalization.result.show}$functionNames$variableNames" 
