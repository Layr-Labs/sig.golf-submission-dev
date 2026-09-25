import Mathlib
namespace SigGolfCandidate.Hypertree.BalancedPacked
set_option maxHeartbeats 1000000

def mask : Nat → Nat
  | 0 => 0
  | k+1 => 7 + 256 * mask k

theorem flip_rec (k : Nat) : ∀ n : Nat, n < 256^k →
    (∀ i, i < k → n / 256^i % 256 ≤ 7) →
    n ≤ mask k ∧ ∀ i, i < k →
      (mask k - n) / 256^i % 256 = 7 - n / 256^i % 256 := by
  induction k with
  | zero =>
    intro n hn _
    have nzero : n = 0 := by simpa using hn
    subst n
    constructor
    · simp [mask]
    · intro i hi; omega
  | succ k ih =>
    intro n hn hb
    have hq : n / 256 < 256^k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ, Nat.mul_comm] using hn
    have hbq : ∀ i, i < k → (n/256) / 256^i % 256 ≤ 7 := by
      intro i hi
      have h := hb (i+1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h
    obtain ⟨qle, qdigits⟩ := ih (n/256) hq hbq
    have hd : n % 256 ≤ 7 := by simpa using hb 0 (by omega)
    have ndec : n = 256 * (n/256) + n%256 := by omega
    have hle : n ≤ mask (k+1) := by simp only [mask]; omega
    refine ⟨hle, ?_⟩
    intro i hi
    have hsub : mask (k+1) - n = (7 - n%256) + 256*(mask k - n/256) := by
      simp only [mask]
      omega
    rw [hsub]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      omega
    | succ j =>
      have hj : j < k := by omega
      have hr : 7 - n%256 < 256 := by omega
      have hquot : ((7-n%256)+256*(mask k-n/256))/256 = mask k-n/256 := by omega
      have dpow : 256^(j+1) = 256*256^j := by simp [pow_succ, Nat.mul_comm]
      rw [dpow, ← Nat.div_div_eq_div_mul, hquot]
      rw [← Nat.div_div_eq_div_mul]
      exact qdigits j hj
#print axioms flip_rec

theorem mask8_eq : mask 8 = 0x0707070707070707 := by decide

private theorem pow_byte (i : Nat) : 2 ^ (8*i) = 256^i := by
  rw [pow_mul]
  norm_num

theorem flip_word_byte (w : BitVec 64)
    (hb : ∀ i : Fin 8, (w.extractLsb' (8*i.val) 8).toNat ≤ 7)
    (i : Fin 8) :
    ((0x0707070707070707#64 - w).extractLsb' (8*i.val) 8).toNat =
      7 - (w.extractLsb' (8*i.val) 8).toNat := by
  have hbytes : ∀ j, j < 8 → w.toNat / 256^j % 256 ≤ 7 := by
    intro j hj
    have h := hb ⟨j,hj⟩
    simpa only [BitVec.extractLsb', BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, pow_byte] using h
  obtain ⟨hle, hrec⟩ := flip_rec 8 w.toNat (by
    simpa only [show 256^8 = 2^64 by decide] using w.isLt) hbytes
  have hmask : (0x0707070707070707#64).toNat = mask 8 := by
    rw [mask8_eq]
    decide
  have hmaskLt : mask 8 < 2^64 := by rw [mask8_eq]; decide
  have hsub : (0x0707070707070707#64 - w).toNat = mask 8 - w.toNat := by
    rw [BitVec.toNat_sub, hmask]
    have hx := w.isLt
    omega
  simpa only [BitVec.extractLsb', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, pow_byte, hsub] using hrec i.val i.isLt
#print axioms flip_word_byte

theorem flip_digit (d : Nat) (hd : d < 8) :
    (BitVec.ofNat 8 d ^^^ 7#8) = BitVec.ofNat 8 (7-d) := by
  interval_cases d <;> decide
#print axioms flip_digit
end SigGolfCandidate.Hypertree.BalancedPacked
