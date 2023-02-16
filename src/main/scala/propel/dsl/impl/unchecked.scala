package propel
package dsl.impl

import dsl.scala.*

object Unchecked:
  trait PropertyAnnotation[+P, -A <: (_, _)] extends (P := A)
  trait AnnotatedFunction[+A <: _ := _, R] extends (A =>: R)

  trait FromFunction:
    this: =>:.type =>

    import scala.language.implicitConversions

    implicit def fromFunction[A, B, R](f: (A, B) => R): Any := (A, B) =>: R =
      new AnnotatedFunction[PropertyAnnotation[Any, (A, B)], R]:
        val a: PropertyAnnotation[Any, (A, B)] { type Arguments = (A, B) } =
          new PropertyAnnotation[Any, (A, B)] { type Arguments = (A, B) }
        def apply(v: (A, B)): R = f(v._1, v._2)

    implicit def fromFunction[A, B, R](f: A => B => R): Any := (A, B) =>: R =
      new AnnotatedFunction[PropertyAnnotation[Any, (A, B)], R]:
        val a: PropertyAnnotation[Any, (A, B)] { type Arguments = (A, B) } =
          new PropertyAnnotation[Any, (A, B)] { type Arguments = (A, B) }
        def apply(v: (A, B)): R = f(v._1)(v._2)
