package propel

import propel.dsl.scala.*

// functor map

val fmap = prop.rec[(Nat => Nat) => Option[Nat] => Option[Nat]]: fmap =>
  props(
    // identity
    (x: Option[Nat]) =>
      fmap(y => y)(x) =:= x,

    // composition
    (x: Option[Nat], f: Nat => Nat, g: Nat => Nat) =>
      fmap(y => f(g(y)))(x) =:= fmap(f)(fmap(g)(x))
  ):
    f => x => x match
      case Some(x) => Some(f(x))
      case _ => None


// semigroup operation

val op = prop[Assoc := (Option[Nat], Option[Nat]) =>: Option[Nat]]:
  case (None, y) => y
  case (x, None) => x
  case (Some(x), Some(y)) => Some(addNat(x, y))


// monad pure and bind

val pure = prop.rec[Nat => Option[Nat]]: pure =>
  x => Some(x)

val bind = prop.rec[Option[Nat] => (Nat => Option[Nat]) => Option[Nat]]: bind =>
  props(
    // left identity
    (x: Nat, f: Nat => Option[Nat]) =>
      bind(pure(x))(f) =:= f(x),

    // right identity
    (x: Nat, m: Option[Nat]) =>
      bind(m)(pure) =:= m,

    // associativity
    (x: Nat, m: Option[Nat], f: Nat => Option[Nat], g: Nat => Option[Nat]) =>
      bind(bind(m)(f))(g) =:= bind(m)(x => bind(f(x))(g))
  ):
    x => f => x match
      case Some(x) => f(x)
      case _ => None
