package propel
package dsl.impl

import dsl.scala.*

object Unchecked:
  trait PropertyAnnotation[+P, -A <: (?, ?)] extends (P := A)
  trait AnnotatedFunction[+A <: ? := ?, R] extends (A =>: R)
