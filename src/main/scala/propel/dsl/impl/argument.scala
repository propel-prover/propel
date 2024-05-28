package propel
package dsl.impl

import dsl.scala.*

type Argument[A <: ? := ?, N <: (1 | 2)] = A match
  case (p := a) => a match
    case (a, b) => N match
      case 1 => a
      case 2 => b
