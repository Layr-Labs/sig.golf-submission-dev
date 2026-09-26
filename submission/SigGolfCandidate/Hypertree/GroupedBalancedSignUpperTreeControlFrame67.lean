import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStart67
import SigGolfCandidate.TraceDeterminism

/-! Control words untouched by the upper Merkle callee's stack entry. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeControlFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

def Safe (a : Word) : Prop :=
  a = 0x81058 ∨ a = 0x81060 ∨ a = 0x810f8 ∨
  a = 0x81090 ∨ a = 0x81098 ∨ a = 0x810a0 ∨ a = 0x810e8

theorem safe_facts (a : Word) (safe : Safe a) :
    0x81000 ≤ a.toNat ∧ a.toNat < 0x83000 ∧ a.toNat < 0x90000 ∧
    a ≠ 0x81000 ∧ a ≠ 0x81008 ∧ a ≠ 0x81010 ∧ a ≠ 0x81018 ∧
    a ≠ 0x81050 ∧ a ≠ 0x810c0 ∧ a ≠ 0x810c8 ∧ a ≠ 0x810d0 ∧
    a ≠ 0x810d8 ∧ a ≠ 0x810a8 ∧ a ≠ 0x810b0 ∧ a ≠ 0x810b8 := by
  rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem start_frame (hash : Hash) (s ready : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (trace : Trace hash image s 72 72 0 0 ready)
    (a : Word) (safe : Safe a) : ready.getMem a=s.getMem a := by
  let called := GroupedBalancedSignUpperTreeCall67.called s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let initialized := GroupedBalancedSignBottomTreeInit67.initState entered
  have callSteps := GroupedBalancedSignUpperTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignUpperTreeCall67.call_pc s pc
  have callSp : called.getReg .x2=0xfff7e0 ∨ called.getReg .x2=0xfff700 := by
    rw [GroupedBalancedSignUpperTreeCall67.call_sp]
    exact sp
  have entrySteps := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc callSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initSteps := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude initialized initPc
  have builtTrace : Trace hash image s 72 72 0 0 built := by
    have combined := (((OrdinarySteps.trace (hash := hash) callSteps).trans
      (OrdinarySteps.trace (hash := hash) entrySteps)).trans
      (OrdinarySteps.trace (hash := hash) initSteps)).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  obtain ⟨hi,lo,low,ne00,ne08,ne10,ne18,ne50,neC0,neC8,neD0,
    neD8,neA8,neB0,neB8⟩ := safe_facts a safe
  have neSlot : a ≠ called.getReg .x2-16 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [GroupedBalancedSignUpperTreeCall67.call_sp] at hn
    have slotHigh : 0x90000 ≤ (s.getReg .x2-16).toNat := by
      rcases sp with h | h <;> rw [h] <;> decide
    omega
  rw [same,
    preludeFrame a ne08 ne10 ne18 neA8 neB0 neB8,
    GroupedBalancedSignBottomTreeInitData67.init_frame entered a
      neC0 neC8 neD0,
    GroupedBalancedSignBottomTreeEntryData67.entry_frame called a
      neSlot ne50,
    GroupedBalancedSignUpperTreeCall67.call_mem]

theorem height_step_frame (hash : Hash) (s next : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1 < heightMax)
    (maxBound : heightMax = 3 ∨ heightMax = 4)
    (witnessBound : witnessBase+16*heightMax+16 ≤ 0x80000)
    (witnessAligned : witnessBase % 8 = 0)
    (positive : 0 < limit) (small : limit ≤ 8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit next)
    (a : Word) (safe : Safe a) : next.getMem a=s.getMem a := by
  have hb : height < 10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16 ≤ 0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have doneLevel : done.getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.levelWord
  have doneMax : done.getMem 0x81060 = BitVec.ofNat 64 heightMax := by
    rw [parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.maxLevel
  let shifted := GroupedBalancedSignBottomTreeLevelControl67.transitionState done
  have transitionTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have shiftedPc : shifted.pc=0x1e04 := by
    have h := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc done
      heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
    rw [h]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude shifted shiftedPc
  have builtTrace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit built := by
    have combined := (parentTrace.trans transitionTrace).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> omega
  have same := Trace.deterministic trace builtTrace
  obtain ⟨hi,lo,_,ne00,ne08,ne10,ne18,ne50,neC0,neC8,neD0,
    neD8,neA8,neB0,neB8⟩ := safe_facts a safe
  rw [same,
    preludeFrame a ne08 ne10 ne18 neA8 neB0 neB8,
    GroupedBalancedSignBottomTreeLevelData67.frame done a
      neC0 neC8 neD0 ne00 ne50,
    parentFrame a ⟨hi,lo,ne08,neD8⟩]

#print axioms height_step_frame

theorem terminal_frame (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16 ≤ 0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s 150 157 1 1 final)
    (a : Word) (safe : Safe a) : final.getMem a=s.getMem a := by
  have hb : height < 10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16 ≤ 0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  let shifted := GroupedBalancedSignBottomTreeLevelControl67.transitionState done
  have transitionTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have builtTrace : Trace hash image s 150 157 1 1 shifted := by
    have combined := parentTrace.trans transitionTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace builtTrace
  obtain ⟨hi,lo,_,ne00,ne08,_,_,ne50,neC0,neC8,neD0,
    neD8,_,_,_⟩ := safe_facts a safe
  rw [same,
    GroupedBalancedSignBottomTreeLevelData67.frame done a
      neC0 neC8 neD0 ne00 ne50,
    parentFrame a ⟨hi,lo,ne08,neD8⟩]

#print axioms terminal_frame

#print axioms start_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeControlFrame67
