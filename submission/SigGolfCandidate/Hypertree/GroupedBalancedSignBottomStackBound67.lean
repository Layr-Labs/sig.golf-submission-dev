import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvance67

/-! The 1024 bottom leaves occupy 0x83000 through 0x86fff. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackBound67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

def stack0 (n : Word) : Word := (n <<< 4) + 0x83000

theorem stack0_nat (n : Word) (h : n.toNat < 1024) :
    (stack0 n).toNat = 0x83000 + 16 * n.toNat := by
  have hshift : (n <<< 4).toNat = 16 * n.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hm : n.toNat * 2 ^ 4 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hm]
    omega
  simp only [stack0,BitVec.toNat_add,hshift]
  have hadd : (16 * n.toNat + 0x83000) < 2 ^ 64 := by omega
  change (16 * n.toNat + 536576) % 2 ^ 64 = 536576 + 16 * n.toNat
  rw [Nat.mod_eq_of_lt hadd]
  omega

theorem stack0_range (n : Word) (h : n.toNat < 1024) :
    0x83000 ≤ (stack0 n).toNat ∧ (stack0 n).toNat + 16 ≤ 0x87000 := by
  rw [stack0_nat n h]
  omega

theorem stack8_nat (n : Word) (h : n.toNat < 1024) :
    (stack0 n + 8).toNat = (stack0 n).toNat + 8 := by
  have hr := stack0_range n h
  rw [BitVec.toNat_add]
  change ((stack0 n).toNat + 8) % 18446744073709551616 =
    (stack0 n).toNat + 8
  rw [Nat.mod_eq_of_lt (by omega)]

theorem below_stack (n a : Word) (hn : n.toNat < 1024)
    (ha : a.toNat < 0x83000) : a ≠ stack0 n ∧ a ≠ stack0 n + 8 := by
  have hr := stack0_range n hn
  have h8 := stack8_nat n hn
  constructor
  · intro eq
    have h := congrArg BitVec.toNat eq
    omega
  · intro eq
    have h := congrArg BitVec.toNat eq
    omega

theorem outside_stack (n a : Word) (hn : n.toNat < 1024)
    (ha : a.toNat < 0x83000 ∨ 0x87000 ≤ a.toNat) :
    a ≠ stack0 n ∧ a ≠ stack0 n + 8 := by
  rcases ha with low | high
  · exact below_stack n a hn low
  · have hr := stack0_range n hn
    have h8 := stack8_nat n hn
    constructor
    · intro eq
      have heq := congrArg BitVec.toNat eq
      omega
    · intro eq
      have heq := congrArg BitVec.toNat eq
      omega

theorem stack0_ne_stack8 (n : Word) (h : n.toNat < 1024) :
    stack0 n ≠ stack0 n + 8 := by
  intro eq
  have heq := congrArg BitVec.toNat eq
  rw [stack8_nat n h] at heq
  omega

theorem stack0_valid (n : Word) (h : n.toNat < 1024) :
    accessValid (stack0 n) 8 = true ∧
    accessValid (stack0 n + 8) 8 = true := by
  have hr := stack0_range n h
  have ha : (stack0 n).toNat % 8 = 0 := by
    rw [stack0_nat n h]
    omega
  have hplus := stack8_nat n h
  have hlim : (stack0 n).toNat + 16 ≤ MEMORY_BYTES := by
    change (stack0 n).toNat + 16 ≤ 16777216
    omega
  have h0 : accessValid (stack0 n) 8 = true := by
    simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,ha⟩
  have h8 : accessValid (stack0 n + 8) 8 = true := by
    simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
    rw [hplus]
    constructor <;> omega
  exact ⟨h0,h8⟩

#print axioms stack0_nat
#print axioms stack0_range
#print axioms stack8_nat
#print axioms below_stack
#print axioms outside_stack
#print axioms stack0_ne_stack8
#print axioms stack0_valid
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackBound67
