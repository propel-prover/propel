package propel

import propel.dsl.scala.*

enum Num:
  case Zero
  case Bit0(num: Num)
  case Bit1(num: Num)

val eqNum = prop.rec[(Refl & Sym & Trans & Antisym) := (Num, Num) =>: Boolean] { eqNum => (x, y) =>
  (x, y) match
    case (Num.Zero, Num.Zero) => true
    case (Num.Bit0(x), Num.Bit0(y)) => eqNum(x, y)
    case (Num.Bit1(x), Num.Bit1(y)) => eqNum(x, y)
    case _ => false
}

val maxNum = prop.rec[(Comm & Assoc & Sel) := (Num, Num) =>: Num] { maxNum => (x, y) =>
  (x, y) match
    case (Num.Zero, y) => y
    case (x, Num.Zero) => x
    case (Num.Bit0(x), Num.Bit0(y)) => Num.Bit0(maxNum(x, y))
    case (Num.Bit1(x), Num.Bit1(y)) => Num.Bit1(maxNum(x, y))
    case (Num.Bit0(x), Num.Bit1(y)) => if maxNum(x, y) == y then Num.Bit1(y) else Num.Bit0(x)
    case (Num.Bit1(x), Num.Bit0(y)) => if maxNum(x, y) == x then Num.Bit1(x) else Num.Bit0(y)
}

val leqNum = prop.rec[(Refl & Antisym & Conn & Trans) := (Num, Num) =>: Boolean] { leqNum => (x, y) =>
  (x, y) match
    case (Num.Zero, _) => true
    case (_, Num.Zero) => false
    case (Num.Bit0(x), Num.Bit0(y)) => leqNum(x, y)
    case (Num.Bit0(x), Num.Bit1(y)) => leqNum(x, y)
    case (Num.Bit1(x), Num.Bit0(y)) => leqNum(x, y) && !eqNum(x, y)
    case (Num.Bit1(x), Num.Bit1(y)) => leqNum(x, y)
}

def leqNumAlt = prop.rec[(Refl & Antisym & Conn & Trans) := (Num, Num) =>: Boolean] { leqNumAlt => (x, y) =>
  (x, y) match
    case (Num.Zero, _) => true
    case (_, Num.Zero) => false
    case (Num.Bit0(x), Num.Bit0(y)) => leqNumAlt(x, y)
    case (Num.Bit1(x), Num.Bit1(y)) => leqNumAlt(x, y)
    case (Num.Bit0(x), Num.Bit1(y)) => leqNumAlt(x, y)
    case (Num.Bit1(x), Num.Bit0(y)) => !leqNumAlt(y, x)
}

def maxNumAlt = prop[(Comm & Assoc & Sel) := (Num, Num) =>: Num] { (x, y) =>
  if leqNumAlt(x, y) then y else x
}
