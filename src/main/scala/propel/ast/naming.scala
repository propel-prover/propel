package propel
package ast

import ast.*
import util.*

object Naming:
  def subscript(i: Int) =
    def subscript(i: Int) = i.toString map { c => (c.toInt - '0' + '₀').toChar }
    if i < 0 then "₋" + subscript(-i) else subscript(i)

  def dropSubscript(s: String) =
    (s.reverse dropWhile { c => c >= '₀' && c <= '₋'}).reverseIterator.mkString

  def freshIdent(base: String, used: collection.Set[String]): String =
    def freshIdent(base: String, index: Int): String =
      val ident = base + subscript(index)
      if used.contains(ident) then
        freshIdent(base, index + 1)
      else
        ident
    freshIdent(dropSubscript(base), 1)

  def freshIdent(base: Symbol, used: collection.Set[String]): Symbol =
    Symbol(freshIdent(base.name, used))
end Naming
