package propel
package dsl.scala

import annotation.unchecked.uncheckedVariance


sealed trait Property
sealed trait Comm extends Property
sealed trait Assoc extends Property
sealed trait Idem extends Property
sealed trait Sel extends Property
sealed trait Refl extends Property
sealed trait Irefl extends Property
sealed trait Sym extends Property
sealed trait Antisym extends Property
sealed trait Asym extends Property
sealed trait Conn extends Property
sealed trait Trans extends Property


trait :=[+P, -A <: (_, _)]:
  this: dsl.impl.Unchecked.PropertyAnnotation[P, A] =>
  type Arguments >: A

trait =>:[+A <: _ := _, R] extends ((dsl.impl.Argument[A, 1] @uncheckedVariance, dsl.impl.Argument[A, 2] @uncheckedVariance) => R):
  this: dsl.impl.Unchecked.AnnotatedFunction[A, R] =>

object prop:
  transparent inline def apply[T](using inline function: dsl.impl.Function[T])(inline f: function.Type): T =
    ${ dsl.impl.Checked.check[T]('{f: Any}, recursive = false) }
  transparent inline def rec[T](using inline function: dsl.impl.Function[T])(inline f: T => function.Type): T =
    ${ dsl.impl.Checked.check[T]('{f: Any}, recursive = true) }
