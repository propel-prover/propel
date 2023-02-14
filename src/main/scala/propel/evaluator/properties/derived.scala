package propel
package evaluator
package properties

import ast.*

case class Derived(properties: Properties, normalizations: List[Normalization]) extends Enrichment(Derived)

object Derived extends Enrichment.Extrinsic[Term, Derived]
