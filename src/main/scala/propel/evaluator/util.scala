package propel
package evaluator

import ast.*

package Util:
  def subscript(i: Int) =
    def subscript(i: Int) = i.toString map { c => (c.toInt - '0' + '₀').toChar }
    if i < 0 then "₋" + subscript(-i) else subscript(i)

  def dropSubscript(s: String) =
    (s.reverseIterator dropWhile { c => c >= '₀' && c <= '₋'}).mkString

  def implies(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> b,
    Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))

  def or(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> Data(Constructor.True, List.empty),
    Match(Constructor.False, List.empty) -> b))

  def and(a: Term, b: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> b,
    Match(Constructor.False, List.empty) -> Data(Constructor.False, List.empty)))

  def not(a: Term) = Cases(a, List(
    Match(Constructor.True, List.empty) -> Data(Constructor.False, List.empty),
    Match(Constructor.False, List.empty) -> Data(Constructor.True, List.empty)))
