import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheTick67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainStep67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheFirstChain67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67. -/
section
/-! The first H2 step and all repeated steps of one selected WOTS chain
preserve the returned cache region. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheFirstChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenCacheTick67
open GroupedBalancedKeygenWotsChainRun67
open GroupedBalancedKeygenWotsHashPrelude67
open GroupedBalancedKeygenWotsLoopAdvance67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem first_end_low (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12a8) :
    LowFrame s (firstEnd hash s) := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have dst := (prelude_fields s pc).2.2.2.2.1
  intro address safeAddress
  have different : address ≠ (0x80000 : Word) := by
    simpa using protected_ne address safeAddress 0x80000
      (by decide) (by decide) (by decide)
  have outside : ∀ i : Fin 4,
      address ≠ Signing.wordAddress 0x80020 i.val := by
    intro i
    simpa only [Signing.wordAddress] using
      protected_ne address safeAddress (0x80020+8*i.val)
        (by omega) (by have := i.isLt; omega)
        (by have := i.isLt; omega)
  change (advanceState hashed).getMem address = s.getMem address
  rw [advance_mem,
    GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
      (hash (hashInput prepared)) dst address outside,
    prelude_mem s address, if_neg different]

#print axioms first_end_low

theorem post_selector_low (hash : Hash) (s final : MachineState)
    (maxStep : Nat) (pc : s.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : s.getReg .x21 = 0)
    (trace : Trace hash image s (4 * maxStep + 6)
      (11 * maxStep + 6) maxStep maxStep final) :
    LowFrame s final := by
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
    run_ticks_framed hash next 1 (maxStep - 1)
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
  exact (first_end_low hash s pc).trans restFrame

#print axioms post_selector_low

theorem after_selector_low (hash : Hash) (s t final : MachineState)
    (ordinary maxStep : Nat)
    (path : OrdinarySteps image s ordinary t)
    (prefixFrame : LowFrame s t)
    (pc : t.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : t.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : t.getReg .x21 = 0)
    (trace : Trace hash image s
      (ordinary + (4 * maxStep + 6))
      (ordinary + (11 * maxStep + 6)) maxStep maxStep final) :
    LowFrame s final := by
  obtain ⟨made, tail, _⟩ :=
    post_selector hash t maxStep pc lower upper maxReg zero
  have full : Trace hash image s
      (ordinary + (4 * maxStep + 6))
      (ordinary + (11 * maxStep + 6)) maxStep maxStep made := by
    simpa only [Nat.zero_add] using
      (path.trace (hash := hash)).trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact prefixFrame.trans
    (post_selector_low hash t made maxStep pc lower upper maxReg zero tail)

#print axioms after_selector_low

theorem normal_chain_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 26 47 3 3 final) :
    LowFrame s final := by
  let t := GroupedBalancedKeygenWotsSelector67.selectorState s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.normal_fields s pc not65 not66
  have frame : LowFrame s t := by
    intro address _
    simp [t, GroupedBalancedKeygenWotsSelector67.selectorState,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_low hash s t final 8 3
    (GroupedBalancedKeygenWotsSelectorAll67.normal_steps s pc not65 not66)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special65_chain_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 45 101 8 8 final) :
    LowFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special65 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special65_fields s pc index
  have frame : LowFrame s t := by
    intro address _
    simp [t, GroupedBalancedKeygenWotsSelectorAll67.special65,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_low hash s t final 7 8
    (GroupedBalancedKeygenWotsSelectorAll67.special65_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special66_chain_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 54 124 10 10 final) :
    LowFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special66 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special66_fields s pc index
  have frame : LowFrame s t := by
    intro address _
    simp [t, GroupedBalancedKeygenWotsSelectorAll67.special66,
      execInstrBr, signExtend12, signExtend13, signExtend21]
  exact after_selector_low hash s t final 8 10
    (GroupedBalancedKeygenWotsSelectorAll67.special66_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

#print axioms normal_chain_low
#print axioms special65_chain_low
#print axioms special66_chain_low

theorem wots_prepared_low (s : MachineState) :
    LowFrame s (GroupedBalancedKeygenWotsPrepared67.wotsState s) := by
  intro address safeAddress
  have neq (n : Nat) (large : 0x20060 ≤ n) (upper : n < 0x82000)
      (small : n < 2 ^ 64) :
      address ≠ BitVec.ofNat 64 n := by
    exact protected_ne address safeAddress n large upper small
  have n0 := neq 0x80000 (by omega) (by omega) (by omega)
  have n1 := neq 0x80008 (by omega) (by omega) (by omega)
  have n2 := neq 0x80010 (by omega) (by omega) (by omega)
  have n3 := neq 0x80018 (by omega) (by omega) (by omega)
  have n4 := neq 0x81038 (by omega) (by omega) (by omega)
  simp [GroupedBalancedKeygenWotsPrepared67.wotsState,
    GroupedBalancedKeygenWotsPrepared67.all_mem,
    GroupedBalancedKeygenWotsHeader67.header_mem_other _ address n0,
    GroupedBalancedKeygenWotsHeader67.reset_mem_other _ address n4,
    n1, n2, n3]

theorem regular_from_entry_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 67 88 3 3 final) :
    LowFrame s final := by
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
  exact (wots_prepared_low s).trans
    (normal_chain_low hash ready made readyPC readyNot65 readyNot66 tail)

theorem special65_from_entry_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 86 142 8 8 final) :
    LowFrame s final := by
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
  exact (wots_prepared_low s).trans
    (special65_chain_low hash ready made readyPC readyIndex tail)

theorem special66_from_entry_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 95 165 10 10 final) :
    LowFrame s final := by
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
  exact (wots_prepared_low s).trans
    (special66_chain_low hash ready made readyPC readyIndex tail)

#print axioms wots_prepared_low
#print axioms regular_from_entry_low
#print axioms special65_from_entry_low
#print axioms special66_from_entry_low

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheFirstChain67

end

/-! Low-memory frame across the endpoint copy after each direct67 WOTS chain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenCacheTick67
open GroupedBalancedKeygenCacheFirstChain67
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem word_ne_of_lt (n limit : Nat)
    (small : n < limit) (limitBound : limit < 2 ^ 64) :
    (BitVec.ofNat 64 n : Word) ≠ BitVec.ofNat 64 limit := by
  intro eq
  have same := congrArg BitVec.toNat eq
  simp [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt limitBound] at same
  omega

theorem copy_low (s : MachineState) (n : Nat)
    (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    LowFrame s (copyState s) := by
  intro a safeAddress
  have high (m : Nat) (hm : 0x20060 ≤ m) (upper : m < 0x82000)
      (small : m < 2 ^ 64) :
      a ≠ BitVec.ofNat 64 m := by
    exact protected_ne a safeAddress m hm upper small
  have n0 := high 0x81030 (by omega) (by omega) (by omega)
  have n1 : a ≠ address s := by
    rw [address_eq s n counter]
    exact high (0x80800 + 16*n) (by omega) (by omega) (by omega)
  have n2 : a ≠ address s + 8 := by
    rw [address_eq s n counter]
    have eq : BitVec.ofNat 64 (0x80800 + 16*n) + 8 =
        BitVec.ofNat 64 (0x80800 + 16*n + 8) :=
      (BitVec.ofNat_add _ _).symm
    rw [eq]
    exact high (0x80800 + 16*n + 8) (by omega) (by omega) (by omega)
  rw [copy_mem]
  split_ifs with h0 h2 h1 <;> simp_all

theorem regular_step_low (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x11d8) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : s.getReg .x19 = BitVec.ofNat 64 n)
    (trace : Trace hash image s 86 107 3 3 final) :
    LowFrame s final := by
  have not65 : s.getReg .x19 ≠ 65#64 := by
    rw [index]
    exact word_ne_of_lt n 65 small (by decide)
  have not66 : s.getReg .x19 ≠ 66#64 := by
    rw [index]
    exact word_ne_of_lt n 66 (by omega) (by decide)
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.regular_from_entry hash s pc not65 not66
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = BitVec.ofNat 64 n :=
    readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready n (by omega) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 86 107 3 3 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (regular_from_entry_low hash s ready pc not65 not66 first).trans
    (copy_low ready n (by omega) readyWord)

theorem special65_step_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 65#64)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 105 161 8 8 final) :
    LowFrame s final := by
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special65_from_entry hash s pc index
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = 65#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 65 (by decide) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 105 161 8 8 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (special65_from_entry_low hash s ready pc index first).trans
    (copy_low ready 65 (by decide) readyWord)

theorem special66_step_low (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 66#64)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 114 184 10 10 final) :
    LowFrame s final := by
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special66_from_entry hash s pc index
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = 66#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 66 (by decide) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 114 184 10 10 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (special66_from_entry_low hash s ready pc index first).trans
    (copy_low ready 66 (by decide) readyWord)

#print axioms copy_low
#print axioms regular_step_low
#print axioms special65_step_low
#print axioms special66_step_low

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67
