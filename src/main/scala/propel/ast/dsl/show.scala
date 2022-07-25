package propel
package dsl

import impl.*
import ast.*

extension (uniqueNames: AlphaConversion.UniqueNames) def show: String =
  s"UniqueNames(${uniqueNames.expr.show})"

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
