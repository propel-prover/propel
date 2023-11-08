package propel

import propel.dsl.scala.*

case class Pair[T1,T2](fst: T1, snd: T2)

case class V[T](v: T)

def argMin[T] =
  prop[(Antisym := (T, T) =>: Boolean)
       => (Antisym := (T, T) =>: Boolean)
       => (Comm := (T, T) =>: T)
       => T => T => T
       => (Comm := (V[T], V[T]) =>: V[T])] { antisym => someRel => f => d0 => d1 => d2 => (x, y) =>
    (x, y) match
      case (V(x), V(y)) =>
        V((antisym(x, y), antisym(y, x)) match
          case (true, true) => f(x, y)
          case (true, false) => if someRel(x,y) && someRel(y,x) then d1 else d2
          case (false, true) => if someRel(x,y) && someRel(y,x) then d0 else d2
          case (false, false) => d2
          )
  }
