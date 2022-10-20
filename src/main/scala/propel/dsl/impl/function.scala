package propel
package dsl.impl

import dsl.scala.*

sealed trait Function[T]:
  type Type

sealed trait FunctionFallback:
  def create[T, U]: Function.Aux[T, U] = new Function[T] { type Type = U }
  given[T]: Function.Aux[T, T] = create

object Function extends FunctionFallback:
  type Aux[T, U] = Function[T] { type Type = U }

  given[P, A, B, R](using r: Function[R])
  : Function.Aux[
    P := (A, B) =>: R,
    (A, B) => r.Type] = create

  given function1[T0, R](using r: Function[R])
  : Function.Aux[
    T0 => R,
    T0 => r.Type] = create

  given function2[T0, T1, R](using r: Function[R])
  : Function.Aux[
    (T0, T1) => R,
    (T0, T1) => r.Type] = create

  given function3[T0, T1, T2, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2) => R,
    (T0, T1, T2) => r.Type] = create

  given function4[T0, T1, T2, T3, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3) => R,
    (T0, T1, T2, T3) => r.Type] = create

  given function5[T0, T1, T2, T3, T4, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4) => R,
    (T0, T1, T2, T3, T4) => r.Type] = create

  given function6[T0, T1, T2, T3, T4, T5, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5) => R,
    (T0, T1, T2, T3, T4, T5) => r.Type] = create

  given function7[T0, T1, T2, T3, T4, T5, T6, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6) => R,
    (T0, T1, T2, T3, T4, T5, T6) => r.Type] = create

  given function8[T0, T1, T2, T3, T4, T5, T6, T7, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7) => r.Type] = create

  given function9[T0, T1, T2, T3, T4, T5, T6, T7, T8, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8) => r.Type] = create

  given function10[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9) => r.Type] = create

  given function11[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10) => r.Type] = create

  given function12[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11) => r.Type] = create

  given function13[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12) => r.Type] = create

  given function14[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13) => r.Type] = create

  given function15[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14) => r.Type] = create

  given function16[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15) => r.Type] = create

  given function17[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16) => r.Type] = create

  given function18[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17) => r.Type] = create

  given function19[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18) => r.Type] = create

  given function20[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19) => r.Type] = create

  given function21[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20) => r.Type] = create

  given function22[T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, R](using r: Function[R])
  : Function.Aux[
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21) => R,
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21) => r.Type] = create
end Function
