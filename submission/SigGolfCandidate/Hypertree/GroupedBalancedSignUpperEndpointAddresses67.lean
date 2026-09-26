import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedData67


/-! Exact oracle budgets for the 67 direct upper WOTS chains. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCost67
open SigGolfCandidate.Hypertree

def h1Prefix (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, if i%2=0 then 1 else 0

def h2Prefix (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, if i<65 then 3 else if i=65 then 8 else 10

theorem h1_succ (i : Nat) :
    h1Prefix (i+1)=h1Prefix i+(if i%2=0 then 1 else 0) := by
  unfold h1Prefix
  rw [Finset.sum_range_succ]

theorem h2_succ (i : Nat) (hi : i<67) :
    h2Prefix (i+1)=h2Prefix i+
      GroupedBalancedChecksum67.maxDigit ⟨i,hi⟩ := by
  simp [h2Prefix,Finset.sum_range_succ,
    GroupedBalancedChecksum67.maxDigit]

theorem h1_total : h1Prefix 67=34 := by decide
theorem h2_total : h2Prefix 67=213 := by decide
theorem total : h1Prefix 67+h2Prefix 67=247 := by
  rw [h1_total,h2_total]

#print axioms total
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCost67


/-! Nonoverlap facts for the upper WOTS endpoint table. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointAddresses67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

theorem slot_nat (i : Nat) (hi : i<67) (w : Fin 2) :
    (Signing.wordAddress (0x80800+16*i) w.val).toNat =
      0x80800+16*i+8*w.val := by
  unfold Signing.wordAddress
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := w.isLt; omega :
    0x80800+16*i+8*w.val < 2^64)]

theorem slot_eq_flat (i : Nat) (w : Fin 2) :
    Signing.wordAddress (0x80800+16*i) w.val =
      Signing.wordAddress 0x80800 (2*i+w.val) := by
  simp [Signing.wordAddress]
  congr 1
  omega

theorem slot_ne (i j : Nat) (hi : i<67) (hj : j<67)
    (hij : i≠j) (wi wj : Fin 2) :
    Signing.wordAddress (0x80800+16*i) wi.val ≠
      Signing.wordAddress (0x80800+16*j) wj.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [slot_nat i hi wi,slot_nat j hj wj] at h
  have := wi.isLt
  have := wj.isLt
  omega

theorem slot_ne_step (i : Nat) (hi : i<67) (w : Fin 2) :
    Signing.wordAddress (0x80800+16*i) w.val ≠ 0x81038 := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [slot_nat i hi w] at h
  have numeric : (0x81038 : Word).toNat = 0x81038 := by decide
  rw [numeric] at h
  have := w.isLt
  omega

theorem slot_ne_counter (i : Nat) (hi : i<67) (w : Fin 2) :
    Signing.wordAddress (0x80800+16*i) w.val ≠ 0x81030 := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [slot_nat i hi w] at h
  have numeric : (0x81030 : Word).toNat = 0x81030 := by decide
  rw [numeric] at h
  have := w.isLt
  omega

theorem slot_high (i : Nat) (hi : i<67) (w : Fin 2) :
    0x80600 ≤ (Signing.wordAddress (0x80800+16*i) w.val).toNat := by
  rw [slot_nat i hi w]
  omega

theorem slot_before_cache (i : Nat) (hi : i<67) (w : Fin 2) :
    (Signing.wordAddress (0x80800+16*i) w.val).toNat < 0x80d00 := by
  rw [slot_nat i hi w]
  have := w.isLt
  omega

theorem high_ne_slot (a : Word) (i : Nat) (hi : i<67)
    (high : 0x81000 ≤ a.toNat) (w : Fin 2) :
    a ≠ Signing.wordAddress (0x80800+16*i) w.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [slot_nat i hi w] at h
  have := w.isLt
  omega

theorem cache_ne_slot (i : Nat) (hi : i<67) (w k : Fin 2) :
    Signing.wordAddress 0x80d10 w.val ≠
      Signing.wordAddress (0x80800+16*i) k.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  rw [slot_nat i hi k] at h
  fin_cases w <;> simp [Signing.wordAddress] at h <;> omega

#print axioms slot_ne
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointAddresses67
