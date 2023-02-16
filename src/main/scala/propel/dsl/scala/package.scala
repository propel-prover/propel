package propel
package dsl.scala


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

trait =>:[+A <: _ := _, R]:
  this: dsl.impl.Unchecked.AnnotatedFunction[A, R] =>
  val a: A
  def apply(v: a.Arguments): R

object =>: extends dsl.impl.Unchecked.FromFunction

object prop:
  transparent inline def apply[T](using inline function: dsl.impl.Function[T])(inline f: function.Type): T =
    ${ dsl.impl.Checked.check[T]('{f: Any}, recursive = false) }
  transparent inline def rec[T](using inline function: dsl.impl.Function[T])(inline f: T => function.Type): T =
    ${ dsl.impl.Checked.check[T]('{f: Any}, recursive = true) }
