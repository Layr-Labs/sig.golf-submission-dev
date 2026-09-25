import Mathlib

/-! A table-free RV64 candidate for unpacking four radix-eight digits at a time. -/

namespace SigGolfCandidate.Hypertree.SwarDigits

def spread4 (x : BitVec 12) : BitVec 32 := Id.run do
  let mut y := x.zeroExtend 32
  y := (y &&& 0x0000003f#32) ||| ((y &&& 0x00000fc0#32) <<< 10)
  y := (y &&& 0x00070007#32) ||| ((y &&& 0x00380038#32) <<< 5)
  return y

theorem spread4_digits (x : BitVec 12) (i : Fin 4) :
    (spread4 x).extractLsb' (8*i.val) 3 = x.extractLsb' (3*i.val) 3 := by
  fin_cases i <;> simp [spread4] <;> bv_decide

theorem spread4_sum (x : BitVec 12) :
    ((spread4 x * 0x01010101#32) >>> 24).truncate 8 =
      ((x.extractLsb' 0 3).zeroExtend 8) +
      ((x.extractLsb' 3 3).zeroExtend 8) +
      ((x.extractLsb' 6 3).zeroExtend 8) +
      ((x.extractLsb' 9 3).zeroExtend 8) := by
  simp [spread4]
  bv_decide

end SigGolfCandidate.Hypertree.SwarDigits
