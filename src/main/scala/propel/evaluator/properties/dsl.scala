package propel
package evaluator
package properties

import ast.*

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
