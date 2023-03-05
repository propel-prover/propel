package propel

import propel.dsl.scala.*

def zipWith[P >: (Comm & Assoc & Idem), T] =
  prop.rec[(P := (T, T) =>: T) => (P := (List[T], List[T]) =>: List[T])] { zipWith => f => (x, y) =>
    (x, y) match
      case (Nil, y) => y
      case (x, Nil) => x
      case (x :: xs, y :: ys) => f(x, y) :: zipWith(f)(xs, ys)
  }
