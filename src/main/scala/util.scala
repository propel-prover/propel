package util

import scala.collection.{BuildFrom, Factory, IterableOps}
import scala.collection.mutable.Builder

extension [K, V, C, CC[T] <: IterableOnce[T]](iterable: CC[Map[K, V]])
  inline def mergeLeft: Map[K, V] =
    val iterator = iterable.iterator
    if iterator.isEmpty then Map.empty else iterator reduceLeft { _ ++ _ }

extension [T, C, CC0[T] <: IterableOnce[T], CC1[T] <: IterableOps[T, CC1, C]](iterable: CC0[CC1[T]])(using f: Factory[T, CC1[T]])
  inline def mergeLeft: CC1[T] =
    val iterator = iterable.iterator
    if iterator.isEmpty then f.newBuilder.result() else iterator reduceLeft { _ ++ _ }

extension [T, CC[T] <: IterableOnce[T]](iterable: CC[T])
  def mapIfDefined[U, To](f: T => Option[U])(using bf: BuildFrom[CC[T], U, To]): Option[To] =
    val iterator = iterable.iterator
    var builder: Builder[U, To] | Null = bf.newBuilder(iterable)
    while builder != null && iterator.hasNext do
      val mapped = f(iterator.next())
      if mapped.isEmpty then builder = null else builder.addOne(mapped.get)
    if builder == null then None else Some(builder.result())

  def reduceLeftIfDefined(op: (T, T) => Option[T]): Option[T] =
    val iterator = iterable.iterator
    if iterator.isEmpty then None else
      var reduced: Option[T] = Some(iterator.next())
      while !reduced.isEmpty && iterator.hasNext do reduced = op(reduced.get, iterator.next())
      reduced

extension [T, CC[T] <: IterableOnce[T]](iterable: CC[Option[T]])
  inline def sequenceIfDefined[To](using bf: BuildFrom[CC[Option[T]], T, To]): Option[To] =
    iterable.mapIfDefined(identity)
