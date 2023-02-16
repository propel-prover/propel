package propel

import propel.dsl.scala.*


enum Nat:
  case Zero
  case Succ(pred: Nat)

val addNat = prop.rec[(Comm & Assoc) := (Nat, Nat) =>: Nat] { addNat => (x, y) =>
  x match
    case Nat.Zero => y
    case Nat.Succ(x) => Nat.Succ(addNat(x, y))
}

val addMult = prop.rec[(Comm & Assoc) := (Nat, Nat) =>: Nat] { addMult => (x, y) =>
  x match
    case Nat.Zero => Nat.Zero
    case Nat.Succ(x) => addNat(y, addMult(x, y))
}

val leqNat = prop.rec[(Refl & Antisym & Conn & Trans) := (Nat, Nat) =>: Boolean] { leqNat => (x, y) =>
  (x, y) match
    case (Nat.Succ(x), Nat.Succ(y)) => leqNat(x, y)
    case (Nat.Zero, _) => true
    case _ => false
}


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


def zipWith[P >: (Comm & Assoc & Idem), T] =
  prop.rec[(P := (T, T) =>: T) => (P := (List[T], List[T]) =>: List[T])] { zipWith => f => (x, y) =>
    (x, y) match
      case (Nil, y) => y
      case (x, Nil) => x
      case (x :: xs, y :: ys) => f(x, y) :: zipWith(f)(xs, ys)
  }
