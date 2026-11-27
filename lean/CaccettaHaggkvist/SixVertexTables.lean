module

public import CaccettaHaggkvist.KernelCore

@[expose] public section

namespace CaccettaHaggkvist.SixVertex

/-- Sixteen unsigned entries per tree leaf; missing entries read as zero. -/
structure PackedTable where
  start : ℕ
  width : ℕ
  mask : ℕ
  pages : NTree

def PackedTable.get (T : PackedTable) (i : ℕ) : ℕ :=
  cond (Nat.ble T.start i)
    (let j := Nat.sub i T.start
     Nat.land (Nat.shiftRight (T.pages.get (Nat.shiftRight j 4)) (Nat.mul T.width (Nat.land j 15))) T.mask)
    0

def PackedTable.signed (T : PackedTable) (i : ℕ) : ℤ :=
  let v := T.get i
  cond (Nat.beq (Nat.land v 1) 0) (Int.ofNat (Nat.shiftRight v 1)) (Int.negSucc (Nat.shiftRight v 1))

def triangleIndex (a b : ℕ) : ℕ :=
  let hi := Nat.max a b
  Nat.add (Nat.div (Nat.mul hi (Nat.succ hi)) 2) (Nat.min a b)

end CaccettaHaggkvist.SixVertex
