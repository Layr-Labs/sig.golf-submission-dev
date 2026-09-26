import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackBound67

/-! Concrete addresses for the two words of every bottom-tree leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67
open SigGolf
open SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackBound67
set_option maxRecDepth 8192
set_option maxHeartbeats 100000

def slot (i k : Nat) : Word := BitVec.ofNat 64 (0x83000 + 16*i + 8*k)

theorem slot_nat (i k : Nat) (hi : i < 1024) (hk : k < 2) :
    (slot i k).toNat = 0x83000 + 16*i + 8*k := by
  simp only [slot,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem slot0_dynamic (i : Nat) (hi : i < 1024) :
    slot i 0 = stack0 (BitVec.ofNat 64 i) := by
  apply BitVec.toNat_inj.mp
  rw [slot_nat i 0 hi (by decide)]
  have hw : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [stack0_nat _ (by rw [hw]; exact hi),hw]
  omega

theorem slot1_dynamic (i : Nat) (hi : i < 1024) :
    slot i 1 = stack0 (BitVec.ofNat 64 i) + 8 := by
  apply BitVec.toNat_inj.mp
  rw [slot_nat i 1 hi (by decide)]
  have hw : (BitVec.ofNat 64 i).toNat = i := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [stack8_nat _ (by rw [hw]; exact hi),stack0_nat _
    (by rw [hw]; exact hi),hw]

theorem slot_current0 (n : Word) (h : n.toNat < 1024) :
    slot n.toNat 0 = stack0 n := by
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using slot0_dynamic n.toNat h

theorem slot_current1 (n : Word) (h : n.toNat < 1024) :
    slot n.toNat 1 = stack0 n + 8 := by
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using slot1_dynamic n.toNat h

theorem earlier_ne (i j k l : Nat) (hi : i < 1024) (hj : j < i)
    (hk : k < 2) (hl : l < 2) : slot j k ≠ slot i l := by
  intro eq
  have heq := congrArg BitVec.toNat eq
  rw [slot_nat j k (by omega) hk,slot_nat i l hi hl] at heq
  omega

theorem slot_range (i k : Nat) (hi : i < 1024) (hk : k < 2) :
    0x83000 ≤ (slot i k).toNat ∧ (slot i k).toNat < 0x87000 := by
  rw [slot_nat i k hi hk]
  omega

theorem slot_ne_below (i k : Nat) (hi : i < 1024) (hk : k < 2)
    (a : Word) (ha : a.toNat < 0x83000) : slot i k ≠ a := by
  intro eq
  have heq := congrArg BitVec.toNat eq
  have hr := slot_range i k hi hk
  omega

#print axioms slot_nat
#print axioms slot0_dynamic
#print axioms slot1_dynamic
#print axioms slot_current0
#print axioms slot_current1
#print axioms earlier_ne
#print axioms slot_range
#print axioms slot_ne_below
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67
