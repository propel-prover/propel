package propel
package dsl.impl

import dsl.scala.*

object Unchecked:
  trait PropertyAnnotation[+P, -A <: (_, _)] extends (P := A)
  trait AnnotatedFunction[+A <: _ := _, R] extends (A =>: R)
