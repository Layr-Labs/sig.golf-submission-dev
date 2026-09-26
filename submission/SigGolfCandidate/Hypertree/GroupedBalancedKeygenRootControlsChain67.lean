import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsTick67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChain67. -/
section
/-! The keygen WOTS H2 tick preserves both high tree-address words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsTick67
open GroupedBalancedKeygenWotsTickLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def ControlFrame (s t : MachineState) : Prop :=
  t.getMem 0x81010 = s.getMem 0x81010 ∧
  t.getMem 0x81018 = s.getMem 0x81018

theorem ControlFrame.refl (s : MachineState) : ControlFrame s s := ⟨rfl,rfl⟩

theorem ControlFrame.trans {s t u : MachineState}
    (first : ControlFrame s t) (second : ControlFrame t u) :
    ControlFrame s u := ⟨second.1.trans first.1,second.2.trans first.2⟩

theorem tick_next_control (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020) :
    ControlFrame s (tickNext hash s) := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  have one (a : Word) (ne : a ≠ 0x80000)
      (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) :
      (tickNext hash s).getMem a = s.getMem a := by
    rw [tickNext,GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
    rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
      (storeState s) (hash (hashInput (storeState s))) dst a outside]
    rw [store_mem s source a,if_neg ne]
  constructor
  · apply one 0x81010 (by decide)
    intro i
    fin_cases i <;> decide
  · apply one 0x81018 (by decide)
    intro i
    fin_cases i <;> decide

theorem run_ticks_control (hash : Hash) (s final : MachineState)
    (start remaining : Nat) (positive : 0 < remaining)
    (small : start+remaining ≤ 10)
    (pc : s.pc = 0x12c0)
    (step : s.getReg .x21 = BitVec.ofNat 64 start)
    (maxStep : s.getReg .x20 = BitVec.ofNat 64 (start+remaining))
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (trace : Trace hash image s (4*remaining) (11*remaining)
      remaining remaining final) :
    ControlFrame s final := by
  induction remaining generalizing s start final with
  | zero => omega
  | succ t ih =>
    let next := tickNext hash s
    have first := tick_next_trace hash s pc service source bits destination
    have firstFrame := tick_next_control hash s pc source destination
    obtain ⟨nextPCField,nextStepField,nextMaxField,nextReg⟩ :=
      tick_next_fields hash s pc
    have nextStep : next.getReg .x21 = BitVec.ofNat 64 (start+1) := by
      rw [nextStepField,step]
      simp [BitVec.ofNat_add]
    have nextMax : next.getReg .x20 = BitVec.ofNat 64 (start+t+1) := by
      rw [nextMaxField,maxStep]
      congr 1
    have reg (r : Reg) (different : r ≠ .x21) :
        next.getReg r = s.getReg r := nextReg r different
    by_cases done : t = 0
    · subst t
      have same : final = next := by
        apply Trace.deterministic trace
        simpa only [Nat.zero_add,Nat.mul_one] using first
      rw [same]
      exact firstFrame
    · have nextPC : next.pc = 0x12c0 := by
        have ne : (BitVec.ofNat 64 (start+1) : Word) ≠
            BitVec.ofNat 64 (start+t+1) := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : start+1<2^64),
            Nat.mod_eq_of_lt (by omega : start+t+1<2^64)] at hn
          omega
        have cond : s.getReg .x21 + 1 ≠ s.getReg .x20 := by
          rw [step,maxStep]
          simpa [BitVec.ofNat_add,Nat.add_assoc] using ne
        rw [nextPCField,if_pos cond]
      have runResult :=
        GroupedBalancedKeygenWotsRunTicks67.run_ticks hash next
          (start+1) t (by omega) (by omega) nextPC nextStep
          (by simpa only [Nat.add_assoc,Nat.add_comm t 1] using nextMax)
          ((reg .x5 (by decide)).trans service)
          ((reg .x10 (by decide)).trans source)
          ((reg .x11 (by decide)).trans bits)
          ((reg .x12 (by decide)).trans destination)
      obtain ⟨other,rest,otherPC,otherStep,otherReg,
        otherCounter,otherLevel,otherLeaf⟩ := runResult
      have made : Trace hash image s (4*(t+1)) (11*(t+1))
          (t+1) (t+1) other := by
        simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,
          Nat.add_comm,Nat.add_left_comm] using first.trans rest
      have same : final = other := Trace.deterministic trace made
      rw [same]
      exact firstFrame.trans (ih next other (start+1) (by omega)
        (by omega) nextPC nextStep
        (by simpa only [Nat.add_assoc,Nat.add_comm t 1] using nextMax)
        ((reg .x5 (by decide)).trans service)
        ((reg .x10 (by decide)).trans source)
        ((reg .x11 (by decide)).trans bits)
        ((reg .x12 (by decide)).trans destination) rest)

#print axioms run_ticks_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsTick67

end

/-! Both high tree-address words survive each keygen WOTS chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenWotsChainRun67
open GroupedBalancedKeygenWotsHashPrelude67
open GroupedBalancedKeygenWotsLoopAdvance67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem first_end_control (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12a8) : ControlFrame s (firstEnd hash s) := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have dst := (prelude_fields s pc).2.2.2.2.1
  have one (a : Word) (ne : a ≠ 0x80000)
      (outside : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) :
      (firstEnd hash s).getMem a = s.getMem a := by
    change (advanceState hashed).getMem a = s.getMem a
    rw [advance_mem,
      GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
        (hash (hashInput prepared)) dst a outside,
      prelude_mem s a,if_neg ne]
  constructor
  · apply one 0x81010 (by decide)
    intro i; fin_cases i <;> decide
  · apply one 0x81018 (by decide)
    intro i; fin_cases i <;> decide

theorem post_selector_control (hash : Hash) (s final : MachineState)
    (maxStep : Nat) (pc : s.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : s.getReg .x21 = 0)
    (trace : Trace hash image s (4*maxStep+6) (11*maxStep+6)
      maxStep maxStep final) : ControlFrame s final := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  let next := advanceState hashed
  obtain ⟨readyPC,service,source,bits,destination,
    _,readyMax,readyZero⟩ := prelude_fields s pc
  have first : Trace hash image s 8 15 1 1 hashed := by
    simpa only [image,GroupedBalancedKeygenWotsFirstHash67.image,
      hashed,prepared] using GroupedBalancedKeygenWotsFirstHash67.hash_call hash s pc
  have hashedPC : hashed.pc = 0x12c8 := by
    simp [hashed,prepared,writeHash,readyPC]
  have second : Trace hash image hashed 2 2 0 0 next := by
    simpa only [image,GroupedBalancedKeygenWotsLoopAdvance67.image,next]
      using (advance_steps hashed hashedPC).trace (hash := hash)
  have hashedReg (r : Reg) : hashed.getReg r = prepared.getReg r := by
    simp [hashed,writeHash,MachineState.getReg_setPC]
  have fields := advance_fields hashed hashedPC
  have nextPC : next.pc = 0x12c0 := by
    have ne : (1 : Word) ≠ BitVec.ofNat 64 maxStep := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : maxStep < 2^64)] at hn
      omega
    calc
      next.pc = (if hashed.getReg .x21+1 ≠ hashed.getReg .x20 then 0x12c0 else 0x12d0) := fields.1
      _ = (if (0 : Word)+1 ≠ BitVec.ofNat 64 maxStep then 0x12c0 else 0x12d0) := by
        rw [hashedReg .x21,hashedReg .x20,readyZero,readyMax,zero,maxReg]
      _ = 0x12c0 := by
        have cond : (0 : Word)+1 ≠ BitVec.ofNat 64 maxStep := by
          simpa using ne
        exact if_pos cond
  have nextStep : next.getReg .x21 = BitVec.ofNat 64 1 := by
    rw [fields.2.1,hashedReg .x21,readyZero,zero]
    decide
  have nextMax : next.getReg .x20 = BitVec.ofNat 64 maxStep := by
    rw [fields.2.2.1,hashedReg .x20,readyMax,maxReg]
  have nextReg (r : Reg) (different : r ≠ .x21) :
      next.getReg r = prepared.getReg r := by
    rw [advance_reg_stable hashed r different,hashedReg]
  have countEq : 1+(maxStep-1)=maxStep := by omega
  obtain ⟨made,rest,_,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenWotsRunTicks67.run_ticks hash next 1 (maxStep-1)
      (by omega) (by omega) nextPC nextStep
      (by simpa only [countEq] using nextMax)
      ((nextReg .x5 (by decide)).trans service)
      ((nextReg .x10 (by decide)).trans source)
      ((nextReg .x11 (by decide)).trans bits)
      ((nextReg .x12 (by decide)).trans destination)
  have madeTrace : Trace hash image s (4*maxStep+6)
      (11*maxStep+6) maxStep maxStep made := by
    have full := (first.trans second).trans rest
    convert full using 1 <;> omega
  have same : final = made := Trace.deterministic trace madeTrace
  rw [same]
  exact (first_end_control hash s pc).trans
    (run_ticks_control hash next made 1 (maxStep-1)
      (by omega) (by omega) nextPC nextStep
      (by simpa only [countEq] using nextMax)
      ((nextReg .x5 (by decide)).trans service)
      ((nextReg .x10 (by decide)).trans source)
      ((nextReg .x11 (by decide)).trans bits)
      ((nextReg .x12 (by decide)).trans destination) rest)

#print axioms post_selector_control

theorem after_selector_control (hash : Hash) (s t final : MachineState)
    (ordinary maxStep : Nat) (path : OrdinarySteps image s ordinary t)
    (prefixFrame : ControlFrame s t)
    (pc : t.pc = 0x12a8) (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : t.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : t.getReg .x21 = 0)
    (trace : Trace hash image s (ordinary+(4*maxStep+6))
      (ordinary+(11*maxStep+6)) maxStep maxStep final) :
    ControlFrame s final := by
  obtain ⟨made,tail,_,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.post_selector hash t maxStep
      pc lower upper maxReg zero
  have full : Trace hash image s (ordinary+(4*maxStep+6))
      (ordinary+(11*maxStep+6)) maxStep maxStep made := by
    simpa only [Nat.zero_add] using (path.trace (hash := hash)).trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact prefixFrame.trans
    (post_selector_control hash t made maxStep pc lower upper maxReg zero tail)

theorem normal_chain_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 26 47 3 3 final) :
    ControlFrame s final := by
  let t := GroupedBalancedKeygenWotsSelector67.selectorState s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.normal_fields s pc not65 not66
  have frame : ControlFrame s t := by
    constructor <;> simp [t,GroupedBalancedKeygenWotsSelector67.selectorState,
      execInstrBr,signExtend12,signExtend13,signExtend21]
  exact after_selector_control hash s t final 8 3
    (GroupedBalancedKeygenWotsSelectorAll67.normal_steps s pc not65 not66)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special65_chain_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c) (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 45 101 8 8 final) :
    ControlFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special65 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special65_fields s pc index
  have frame : ControlFrame s t := by
    constructor <;> simp [t,GroupedBalancedKeygenWotsSelectorAll67.special65,
      execInstrBr,signExtend12,signExtend13,signExtend21]
  exact after_selector_control hash s t final 7 8
    (GroupedBalancedKeygenWotsSelectorAll67.special65_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

theorem special66_chain_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x127c) (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 54 124 10 10 final) :
    ControlFrame s final := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special66 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special66_fields s pc index
  have frame : ControlFrame s t := by
    constructor <;> simp [t,GroupedBalancedKeygenWotsSelectorAll67.special66,
      execInstrBr,signExtend12,signExtend13,signExtend21]
  exact after_selector_control hash s t final 8 10
    (GroupedBalancedKeygenWotsSelectorAll67.special66_steps s pc index)
    frame tpc (by decide) (by decide) tmax tzero (by simpa using trace)

#print axioms normal_chain_control

theorem wots_prepared_control (s : MachineState) :
    ControlFrame s (GroupedBalancedKeygenWotsPrepared67.wotsState s) := by
  constructor <;>
    simp [GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]

theorem regular_from_entry_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (trace : Trace hash image s 67 88 3 3 final) :
    ControlFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  obtain ⟨made,tail,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.normal_chain hash ready readyPC
      (by rw [readyX19]; exact not65)
      (by rw [readyX19]; exact not66)
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 67 88 3 3 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_control s).trans
    (normal_chain_control hash ready made readyPC
      (by rw [readyX19]; exact not65)
      (by rw [readyX19]; exact not66) tail)

theorem special65_from_entry_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8) (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 86 142 8 8 final) :
    ControlFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 65#64 := readyX19.trans index
  obtain ⟨made,tail,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special65_chain hash ready readyPC readyIndex
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 86 142 8 8 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_control s).trans
    (special65_chain_control hash ready made readyPC readyIndex tail)

theorem special66_from_entry_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8) (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 95 165 10 10 final) :
    ControlFrame s final := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 66#64 := readyX19.trans index
  obtain ⟨made,tail,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special66_chain hash ready readyPC readyIndex
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  have full : Trace hash image s 95 165 10 10 made := by
    simpa only [Nat.reduceAdd] using first.trans tail
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact (wots_prepared_control s).trans
    (special66_chain_control hash ready made readyPC readyIndex tail)

#print axioms regular_from_entry_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChain67
