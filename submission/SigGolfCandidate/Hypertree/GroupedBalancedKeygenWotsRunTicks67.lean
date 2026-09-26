import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTickLoop67

/-! Every H2 step of a WOTS chain reaches the next-chain branch in finite time. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTickLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem word_succ (n : Nat) :
    (BitVec.ofNat 64 n : Word) + 1 = BitVec.ofNat 64 (n+1) := by
  simp [BitVec.ofNat_add]

private theorem word_ne (a b : Nat) (ha : a < b) (hb : b ≤ 10) :
    (BitVec.ofNat 64 a : Word) ≠ BitVec.ofNat 64 b := by
  intro eq
  have same := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : a < 2^64),
    Nat.mod_eq_of_lt (by omega : b < 2^64)] at same
  omega

theorem run_ticks (hash : Hash) (s : MachineState)
    (start remaining : Nat) (positive : 0 < remaining)
    (small : start+remaining ≤ 10)
    (pc : s.pc = 0x12c0)
    (step : s.getReg .x21 = BitVec.ofNat 64 start)
    (maxStep : s.getReg .x20 = BitVec.ofNat 64 (start+remaining))
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    ∃ final,
      Trace hash image s (4*remaining) (11*remaining)
        remaining remaining final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x21 = BitVec.ofNat 64 (start+remaining) ∧
      (∀ r : Reg, r ≠ .x21 → final.getReg r = s.getReg r) ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  induction remaining generalizing s start with
  | zero => omega
  | succ remaining ih =>
    let next := tickNext hash s
    have first := tick_next_trace hash s pc service source bits destination
    have fields := tick_next_fields hash s pc
    have nextStep : next.getReg .x21 = BitVec.ofNat 64 (start+1) := by
      rw [fields.2.1,step,word_succ]
    have nextMax : next.getReg .x20 = BitVec.ofNat 64 (start+remaining+1) := by
      rw [fields.2.2.1,maxStep]
      congr 1
    have reg (r : Reg) (different : r ≠ .x21) :
        next.getReg r = s.getReg r := fields.2.2.2 r different
    have counter : next.getMem 0x81030 = s.getMem 0x81030 :=
      tick_next_counter hash s pc source destination
    have level : next.getMem 0x81000 = s.getMem 0x81000 :=
      tick_next_level hash s pc source destination
    have leaf : next.getMem 0x81008 = s.getMem 0x81008 :=
      tick_next_leaf hash s pc source destination
    by_cases done : remaining = 0
    · subst remaining
      have nextPC : next.pc = 0x12d0 := by
        rw [fields.1,step,maxStep,word_succ]
        simp
      refine ⟨next,?_,nextPC,?_,reg,counter,level,leaf⟩
      · simpa only [Nat.zero_add,Nat.mul_one] using first
      · simpa only [Nat.zero_add] using nextStep
    · have left : 0 < remaining := by omega
      have nextPC : next.pc = 0x12c0 := by
        rw [fields.1,step,maxStep,word_succ]
        have ne := word_ne (start+1) (start+remaining+1)
          (by omega) (by omega)
        have ne' : (BitVec.ofNat 64 (start+1) : Word) ≠
            BitVec.ofNat 64 (start+(remaining+1)) := by
          simpa only [Nat.add_assoc] using ne
        simp only [if_pos ne']
      have nextService : next.getReg .x5 = 1 := (reg .x5 (by decide)).trans service
      have nextSource : next.getReg .x10 = 0x80000 :=
        (reg .x10 (by decide)).trans source
      have nextBits : next.getReg .x11 = 384 :=
        (reg .x11 (by decide)).trans bits
      have nextDestination : next.getReg .x12 = 0x80020 :=
        (reg .x12 (by decide)).trans destination
      obtain ⟨final,rest,finalPC,finalStep,finalReg,finalCounter,finalLevel,finalLeaf⟩ :=
        ih next (start+1) left (by omega) nextPC nextStep
          (by simpa only [Nat.add_assoc,Nat.add_comm remaining 1] using nextMax)
          nextService nextSource nextBits nextDestination
      refine ⟨final,?_,finalPC,?_,?_,?_,?_,?_⟩
      · simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,
          Nat.add_comm,Nat.add_left_comm] using first.trans rest
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalStep
      · intro r different
        rw [finalReg r different,reg r different]
      · rw [finalCounter,counter]
      · rw [finalLevel,level]
      · rw [finalLeaf,leaf]

#print axioms run_ticks

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67
