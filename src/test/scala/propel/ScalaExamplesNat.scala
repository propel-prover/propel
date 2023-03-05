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

def maxNat = prop[(Comm & Assoc & Sel) := (Nat, Nat) =>: Nat] { (x, y) =>
  if leqNat(x, y) then y else x
}
