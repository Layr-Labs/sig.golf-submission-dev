import SigGolfCandidate.Hypertree.GroupedUniformDecoderCost

namespace SigGolfCandidate.Hypertree.GroupedUniformLimbArithmetic

private abbrev modulus : Nat := 18446744073709551616

def value (hi lo : BitVec 64) : Nat := hi.toNat * modulus + lo.toNat

theorem value_lt (hi lo : BitVec 64) : value hi lo < 2 ^ 128 := by
  have hh := hi.isLt
  have hl := lo.isLt
  dsimp [value, modulus]
  norm_num at hh hl ⊢
  omega

theorem compare (ah al bh bl : BitVec 64) :
    value ah al < value bh bl ↔ ah < bh ∨ (ah = bh ∧ al < bl) := by
  have ha := al.isLt
  have hb := bl.isLt
  simp only [value, modulus, BitVec.lt_def]
  constructor
  · intro h
    by_cases hhi : ah.toNat < bh.toNat
    · exact Or.inl hhi
    · right
      have heq : ah.toNat = bh.toNat := by
        by_contra ne
        omega
      exact ⟨BitVec.eq_of_toNat_eq heq, by omega⟩
  · intro h
    rcases h with h | ⟨heq, h⟩
    · omega
    · subst bh
      omega

private theorem borrow_nat (a b c d : Nat) (hab : b < a)
    (hcd : c < d) (hc : c < modulus) (hd : d < modulus) :
    (a - b - 1) * modulus + (modulus - (d - c)) =
      (a * modulus + c) - (b * modulus + d) := by
  dsimp [modulus] at *
  omega

private theorem no_borrow_nat (a b c d : Nat) (hab : b ≤ a)
    (hcd : d ≤ c) :
    (a - b) * modulus + (c - d) =
      (a * modulus + c) - (b * modulus + d) := by
  dsimp [modulus] at *
  omega

theorem subtract (ah al bh bl : BitVec 64) (h : value bh bl ≤ value ah al) :
    value (ah - bh - (if al < bl then 1 else 0)) (al - bl) =
      value ah al - value bh bl := by
  have hahi := ah.isLt
  have halo := al.isLt
  have hbhi := bh.isLt
  have hblo := bl.isLt
  by_cases borrow : al < bl
  · have hhigh : bh.toNat < ah.toNat := by
      dsimp [value, modulus] at h
      rw [BitVec.lt_def] at borrow
      omega
    have hbh : bh ≤ ah := by rw [BitVec.le_def]; omega
    have hborrow : (1 : BitVec 64) ≤ ah - bh := by
      rw [BitVec.le_def, BitVec.toNat_sub_of_le hbh]
      have hone : (1 : BitVec 64).toNat = 1 := by decide
      rw [hone]
      omega
    simp only [if_pos borrow, value]
    rw [BitVec.toNat_sub_of_lt borrow]
    rw [BitVec.toNat_sub_of_le hborrow, BitVec.toNat_sub_of_le hbh]
    have hone : (1 : BitVec 64).toNat = 1 := by decide
    rw [hone]
    exact borrow_nat _ _ _ _ hhigh (by rw [BitVec.lt_def] at borrow; exact borrow) halo hblo
  · have hhigh : bh.toNat ≤ ah.toNat := by
      dsimp [value, modulus] at h
      rw [BitVec.lt_def] at borrow
      omega
    simp only [if_neg borrow, value]
    rw [BitVec.toNat_sub_of_le (show bl ≤ al by rw [BitVec.le_def]; rw [BitVec.lt_def] at borrow; omega)]
    have hz : ah - bh - (0 : BitVec 64) = ah - bh := BitVec.sub_zero _
    rw [hz]
    rw [BitVec.toNat_sub_of_le (show bh ≤ ah by rw [BitVec.le_def]; omega)]
    exact no_borrow_nat _ _ _ _ hhigh (by rw [BitVec.lt_def] at borrow; omega)

end SigGolfCandidate.Hypertree.GroupedUniformLimbArithmetic
