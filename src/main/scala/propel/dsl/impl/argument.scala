package propel
package dsl.impl

import dsl.scala.*

type Argument[A <: _ := _, N <: (1 | 2)] = A match
  case (p := (a, b)) => N match
    case 1 => a
    case 2 => b
