import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Hypertree.BalancedWord
open SigGolf

def byteMask : BitVec 64 := 0x0707070707070707

/-- Four RV64I instructions suffice: LUI 0x7070; ADDI 0x707;
SLLI 32; OR the shifted and unshifted halves. -/
theorem mask_four_instructions :
    let half : BitVec 64 := ((0x7070 : BitVec 64) <<< 12) + 0x707
    half ||| (half <<< 32) = byteMask := by decide

theorem mask_byte (i : Fin 8) :
    byteMask.extractLsb' (8 * i.val) 8 = (7 : BitVec 8) := by
  fin_cases i <;> decide

theorem extract_xor (left right : BitVec 64) (i : Fin 8) :
    (left ^^^ right).extractLsb' (8 * i.val) 8 =
      left.extractLsb' (8 * i.val) 8 ^^^ right.extractLsb' (8 * i.val) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, bound,
    decide_true, Bool.true_and]

theorem flip_word_byte (word : BitVec 64) (i : Fin 8) :
    (word ^^^ byteMask).extractLsb' (8 * i.val) 8 =
      word.extractLsb' (8 * i.val) 8 ^^^ (7 : BitVec 8) := by
  rw [extract_xor, mask_byte]

theorem flip_digit (digit : Fin 8) :
    (BitVec.ofNat 8 digit.val ^^^ (7 : BitVec 8)) = BitVec.ofNat 8 (7 - digit.val) := by
  fin_cases digit <;> decide

theorem flip_word_digit (word : BitVec 64) (i : Fin 8)
    (digit : Fin 8) (stored : word.extractLsb' (8 * i.val) 8 = BitVec.ofNat 8 digit.val) :
    (word ^^^ byteMask).extractLsb' (8 * i.val) 8 =
      BitVec.ofNat 8 (7 - digit.val) := by
  rw [flip_word_byte, stored, flip_digit]

def lowMask : BitVec 32 := 0x07070707

theorem low_mask_byte (i : Fin 4) :
    lowMask.extractLsb' (8 * i.val) 8 = (7 : BitVec 8) := by
  fin_cases i <;> decide

theorem flip_low_word_byte (word : BitVec 32) (i : Fin 4) :
    (word ^^^ lowMask).extractLsb' (8 * i.val) 8 =
      word.extractLsb' (8 * i.val) 8 ^^^ (7 : BitVec 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bound
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, bound,
    decide_true, Bool.true_and]
  have maskBit := congrArg (fun value : BitVec 8 => value.getLsbD bit) (low_mask_byte i)
  simp only [BitVec.getLsbD_extractLsb', bound, decide_true, Bool.true_and] at maskBit
  rw [maskBit]

end SigGolfCandidate.Hypertree.BalancedWord
