import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67

/-! The repeated keygen H2 tick writes only its high scratch buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsTick67
open GroupedBalancedKeygenWotsTickLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def LowFrame (before after : MachineState) : Prop :=
  ∀ address : Word,
    (address.toNat < 0x20060 ∨ 0x82000 ≤ address.toNat) →
    after.getMem address = before.getMem address

theorem protected_ne (address : Word)
    (safeAddress : address.toNat < 0x20060 ∨ 0x82000 ≤ address.toNat)
    (m : Nat) (lower : 0x20060 ≤ m) (upper : m < 0x82000)
    (small : m < 2 ^ 64) : address ≠ BitVec.ofNat 64 m := by
  intro same
  have value := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at value
  rcases safeAddress with before | after <;> omega

theorem LowFrame.refl (s : MachineState) : LowFrame s s := by
  intro address _
  rfl

theorem LowFrame.trans {s t u : MachineState}
    (first : LowFrame s t) (second : LowFrame t u) : LowFrame s u := by
  intro address bound
  rw [second address bound, first address bound]

theorem tick_next_low (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    LowFrame s (tickNext hash s) := by
  intro address safeAddress
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext, GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst address]
  · have ne : address ≠ (0x80000 : Word) := by
      simpa using protected_ne address safeAddress 0x80000
        (by decide) (by decide) (by decide)
    rw [store_mem s source address]
    simp only [if_neg ne]
  · intro i
    simpa only [Signing.wordAddress] using
      protected_ne address safeAddress (0x80020+8*i.val)
        (by omega) (by have := i.isLt; omega)
        (by have := i.isLt; omega)

#print axioms tick_next_low

theorem run_ticks_framed (hash : Hash) (s : MachineState)
    (start remaining : Nat) (positive : 0 < remaining)
    (small : start + remaining ≤ 10)
    (pc : s.pc = 0x12c0)
    (step : s.getReg .x21 = BitVec.ofNat 64 start)
    (maxStep : s.getReg .x20 = BitVec.ofNat 64 (start + remaining))
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    ∃ final,
      Trace hash image s (4 * remaining) (11 * remaining)
        remaining remaining final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x21 = BitVec.ofNat 64 (start + remaining) ∧
      (∀ r : Reg, r ≠ .x21 → final.getReg r = s.getReg r) ∧
      LowFrame s final := by
  induction remaining generalizing s start with
  | zero => omega
  | succ remaining ih =>
      let next := tickNext hash s
      have first := tick_next_trace hash s pc service source bits destination
      have oneFrame := tick_next_low hash s pc source destination
      obtain ⟨nextPCField, nextStepField, nextMaxField, nextReg⟩ :=
        tick_next_fields hash s pc
      have nextStep : next.getReg .x21 =
          BitVec.ofNat 64 (start + 1) := by
        rw [nextStepField, step]
        simp [BitVec.ofNat_add]
      have nextMax : next.getReg .x20 =
          BitVec.ofNat 64 (start + remaining + 1) := by
        rw [nextMaxField, maxStep]
        congr 1
      have reg (r : Reg) (different : r ≠ .x21) :
          next.getReg r = s.getReg r := nextReg r different
      by_cases done : remaining = 0
      · subst remaining
        have nextPC : next.pc = 0x12d0 := by
          rw [nextPCField, step, maxStep]
          simp [BitVec.ofNat_add]
        refine ⟨next, ?_, nextPC, ?_, reg, oneFrame⟩
        · simpa only [Nat.zero_add, Nat.mul_one] using first
        · simpa only [Nat.zero_add] using nextStep
      · have left : 0 < remaining := by omega
        have nextPC : next.pc = 0x12c0 := by
          have neq : (BitVec.ofNat 64 (start + 1) : Word) ≠
              BitVec.ofNat 64 (start + remaining + 1) := by
            intro same
            have value := congrArg BitVec.toNat same
            simp only [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : start + 1 < 2 ^ 64),
              Nat.mod_eq_of_lt
                (by omega : start + remaining + 1 < 2 ^ 64)] at value
            omega
          have cond : s.getReg .x21 + 1 ≠ s.getReg .x20 := by
            rw [step, maxStep]
            convert neq using 1
            · simp [BitVec.ofNat_add]
            · congr 1
          rw [nextPCField, if_pos cond]
        obtain ⟨final, rest, finalPC, finalStep, finalReg, restFrame⟩ :=
          ih next (start + 1) left (by omega) nextPC nextStep
            (by simpa only [Nat.add_assoc, Nat.add_comm remaining 1]
              using nextMax)
            ((reg .x5 (by decide)).trans service)
            ((reg .x10 (by decide)).trans source)
            ((reg .x11 (by decide)).trans bits)
            ((reg .x12 (by decide)).trans destination)
        refine ⟨final, ?_, finalPC, ?_, ?_, oneFrame.trans restFrame⟩
        · simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using first.trans rest
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using finalStep
        · intro r different
          rw [finalReg r different, reg r different]

#print axioms run_ticks_framed

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheTick67
