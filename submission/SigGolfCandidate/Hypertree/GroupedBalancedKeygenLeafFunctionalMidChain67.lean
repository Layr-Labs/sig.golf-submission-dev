import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheTick67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
import SigGolfCandidate.TraceDeterminism

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidTick67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidChain67. -/
section
/-! H2 ticks leave the endpoint table and paired-seed cache untouched. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsTick67
open GroupedBalancedKeygenWotsTickLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def MidFrame (before after : MachineState) : Prop :=
  ∀ address : Word, 0x80800 ≤ address.toNat → address.toNat < 0x80d20 →
    after.getMem address = before.getMem address

theorem MidFrame.refl (s : MachineState) : MidFrame s s := by
  intro address _ _
  rfl

theorem MidFrame.trans {s t u : MachineState}
    (first : MidFrame s t) (second : MidFrame t u) : MidFrame s u := by
  intro address lower upper
  rw [second address lower upper, first address lower upper]

theorem tick_next_mid (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    MidFrame s (tickNext hash s) := by
  intro address lower upper
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext, GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst address]
  · rw [store_mem s source address, if_neg]
    intro same
    rw [same] at lower
    exact False.elim ((by decide : ¬(0x80800 ≤ (0x80000 : Word).toNat)) lower)
  · intro i
    fin_cases i <;> intro same <;>
      have value := congrArg BitVec.toNat same <;>
      simp [Signing.wordAddress] at value <;> omega

theorem run_ticks_mid (hash : Hash) (s : MachineState)
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
      MidFrame s final := by
  induction remaining generalizing s start with
  | zero => omega
  | succ remaining ih =>
      let next := tickNext hash s
      have first := tick_next_trace hash s pc service source bits destination
      have oneFrame := tick_next_mid hash s pc source destination
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

#print axioms tick_next_mid
#print axioms run_ticks_mid

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidTick67

end

/-! The first H2 step and all repeated steps of one selected WOTS chain
preserve the returned cache region. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalMidTick67
open GroupedBalancedKeygenWotsChainRun67
open GroupedBalancedKeygenWotsHashPrelude67
open GroupedBalancedKeygenWotsLoopAdvance67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem first_end_mid (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12a8) :
    MidFrame s (firstEnd hash s) := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have dst := (prelude_fields s pc).2.2.2.2.1
  intro address lower upper
  have different : address ≠ (0x80000 : Word) := by
    intro same
    rw [same] at lower
    exact (by decide : ¬(0x80800 ≤ (0x80000 : Word).toNat)) lower
  have outside : ∀ i : Fin 4,
      address ≠ Signing.wordAddress 0x80020 i.val := by
    intro i same
    have value := congrArg BitVec.toNat same
    fin_cases i <;> simp [Signing.wordAddress] at value <;> omega
  change (advanceState hashed).getMem address = s.getMem address
  rw [advance_mem,
    GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
      (hash (hashInput prepared)) dst address outside,
    prelude_mem s address, if_neg different]

#print axioms first_end_mid

theorem post_selector_mid (hash : Hash) (s final : MachineState)
    (maxStep : Nat) (pc : s.pc = 0x12a8)
    (mider : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : s.getReg .x21 = 0)
    (trace : Trace hash image s (4 * maxStep + 6)
      (11 * maxStep + 6) maxStep maxStep final) :
    MidFrame s final := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  let next := advanceState hashed
  obtain ⟨readyPC, service, source, bits, destination,
    _, readyMax, readyZero⟩ := prelude_fields s pc
  have first : Trace hash image s 8 15 1 1 hashed := by
    simpa only [image, GroupedBalancedKeygenWotsFirstHash67.image,
      hashed, prepared] using
      GroupedBalancedKeygenWotsFirstHash67.hash_call hash s pc
  have hashedPC : hashed.pc = 0x12c8 := by
    simp [hashed, prepared, writeHash, readyPC]
  have second : Trace hash image hashed 2 2 0 0 next := by
    simpa only [image, GroupedBalancedKeygenWotsLoopAdvance67.image, next]
      using (advance_steps hashed hashedPC).trace (hash := hash)
  have hashedReg (r : Reg) : hashed.getReg r = prepared.getReg r := by
    simp [hashed, writeHash, MachineState.getReg_setPC]
  have fields := advance_fields hashed hashedPC
  have nextPC : next.pc = 0x12c0 := by
    have ne : (1 : Word) ≠ BitVec.ofNat 64 maxStep := by
      intro eq
      have heq := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : maxStep < 2 ^ 64)] at heq
      omega
    calc
      next.pc =
          (if hashed.getReg .x21 + 1 ≠ hashed.getReg .x20
            then 0x12c0 else 0x12d0) := fields.1
      _ = (if (0 : Word) + 1 ≠ BitVec.ofNat 64 maxStep
            then 0x12c0 else 0x12d0) := by
          rw [hashedReg .x21, hashedReg .x20,
            readyZero, readyMax, zero, maxReg]
      _ = 0x12c0 := by
        have cond : (0 : Word) + 1 ≠ BitVec.ofNat 64 maxStep := by
          have add01 : (0 : Word) + 1 = 1 := by decide
          rw [add01]
          exact ne
        exact if_pos cond
  have nextStep : next.getReg .x21 = BitVec.ofNat 64 1 := by
    rw [fields.2.1, hashedReg .x21, readyZero, zero]
    decide
  have nextMax : next.getReg .x20 = BitVec.ofNat 64 maxStep := by
    rw [fields.2.2.1, hashedReg .x20, readyMax, maxReg]
  have nextReg (r : Reg) (different : r ≠ .x21) :
      next.getReg r = prepared.getReg r := by
    rw [advance_reg_stable hashed r different, hashedReg]
  have countEq : 1 + (maxStep - 1) = maxStep := by omega
  obtain ⟨made, rest, _, _, _, restFrame⟩ :=
    run_ticks_mid hash next 1 (maxStep - 1)
      (by omega) (by omega)
      nextPC nextStep (by simpa only [countEq] using nextMax)
      ((nextReg .x5 (by decide)).trans service)
      ((nextReg .x10 (by decide)).trans source)
      ((nextReg .x11 (by decide)).trans bits)
      ((nextReg .x12 (by decide)).trans destination)
  have madeTrace : Trace hash image s (4 * maxStep + 6)
      (11 * maxStep + 6) maxStep maxStep made := by
    have full := (first.trans second).trans rest
    convert full using 1 <;> omega
  have same : final = made := Trace.deterministic trace madeTrace
  rw [same]
  exact (first_end_mid hash s pc).trans restFrame

#print axioms post_selector_mid

theorem after_selector_mid (hash : Hash) (s t final : MachineState)
    (ordinary maxStep : Nat)
    (path : OrdinarySteps image s ordinary t)
    (prefixFrame : MidFrame s t)
    (pc : t.pc = 0x12a8)
    (mider : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : t.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : t.getReg .x21 = 0)
    (trace : Trace hash image s
      (ordinary + (4 * maxStep + 6))
      (ordinary + (11 * maxStep + 6)) maxStep maxStep final) :
    MidFrame s final := by
  obtain ⟨made, tail, _⟩ :=
    post_selector hash t maxStep pc mider upper maxReg zero
  have full : Trace hash image s
      (ordinary + (4 * maxStep + 6))
      (ordinary + (11 * maxStep + 6)) maxStep maxStep made := by
    simpa only [Nat.zero_add] using
      (path.trace (hash := hash)).trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact prefixFrame.trans
    (post_selector_mid hash t made maxStep pc mider upper maxReg zero tail)

#print axioms after_selector_mid

theorem normal_chain_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 26 47 3 3 final) :
    MidFrame s final := by
  let t := GroupedBalancedKeygenWotsSelector67.selectorState s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.normal_fields s pc not65 not66
  have frame : MidFrame s t := by
    intro address _ _
    simp [t, GroupedBalancedKeygenWotsSelector67.selectorState,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_mid hash s t final 8 3
    (GroupedBalancedKeygenWotsSelectorAll67.normal_steps s pc not65 not66)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special65_chain_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 45 101 8 8 final) :
    MidFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special65 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special65_fields s pc index
  have frame : MidFrame s t := by
    intro address _ _
    simp [t, GroupedBalancedKeygenWotsSelectorAll67.special65,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_mid hash s t final 7 8
    (GroupedBalancedKeygenWotsSelectorAll67.special65_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special66_chain_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 54 124 10 10 final) :
    MidFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special66 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special66_fields s pc index
  have frame : MidFrame s t := by
    intro address _ _
    simp [t, GroupedBalancedKeygenWotsSelectorAll67.special66,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_mid hash s t final 8 10
    (GroupedBalancedKeygenWotsSelectorAll67.special66_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

#print axioms normal_chain_mid
#print axioms special65_chain_mid
#print axioms special66_chain_mid

theorem wots_prepared_mid (s : MachineState) :
    MidFrame s (GroupedBalancedKeygenWotsPrepared67.wotsState s) := by
  intro address lower upper
  have lowNe (n : Nat) (small : n < 0x80800) :
      address ≠ BitVec.ofNat 64 n := by
    intro same
    rw [same] at lower
    simp [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n < 2^64)] at lower
    omega
  have highNe (n : Nat) (large : 0x80d20 ≤ n) (small : n < 2^64) :
      address ≠ BitVec.ofNat 64 n := by
    intro same
    rw [same] at upper
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at upper
    omega
  have n0 := lowNe 0x80000 (by omega)
  have n1 := lowNe 0x80008 (by omega)
  have n2 := lowNe 0x80010 (by omega)
  have n3 := lowNe 0x80018 (by omega)
  have n4 := highNe 0x81038 (by omega) (by omega)
  simp [GroupedBalancedKeygenWotsPrepared67.wotsState,
    GroupedBalancedKeygenWotsPrepared67.all_mem,
    GroupedBalancedKeygenWotsHeader67.header_mem_other _ address n0,
    GroupedBalancedKeygenWotsHeader67.reset_mem_other _ address n4,
    n1, n2, n3]

theorem regular_from_entry_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 67 88 3 3 final) :
    MidFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyNot65 : ready.getReg .x19 ≠ 65#64 := by rw [readyX19]; exact not65
  have readyNot66 : ready.getReg .x19 ≠ 66#64 := by rw [readyX19]; exact not66
  obtain ⟨made, tail, _⟩ :=
    normal_chain hash ready readyPC readyNot65 readyNot66
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 67 88 3 3 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_mid s).trans
    (normal_chain_mid hash ready made readyPC readyNot65 readyNot66 tail)

theorem special65_from_entry_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 86 142 8 8 final) :
    MidFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 65#64 := readyX19.trans index
  obtain ⟨made, tail, _⟩ :=
    special65_chain hash ready readyPC readyIndex
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 86 142 8 8 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_mid s).trans
    (special65_chain_mid hash ready made readyPC readyIndex tail)

theorem special66_from_entry_mid (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 95 165 10 10 final) :
    MidFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 66#64 := readyX19.trans index
  obtain ⟨made, tail, _⟩ :=
    special66_chain hash ready readyPC readyIndex
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 95 165 10 10 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_mid s).trans
    (special66_chain_mid hash ready made readyPC readyIndex tail)

#print axioms wots_prepared_mid
#print axioms regular_from_entry_mid
#print axioms special65_from_entry_mid
#print axioms special66_from_entry_mid

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidChain67
