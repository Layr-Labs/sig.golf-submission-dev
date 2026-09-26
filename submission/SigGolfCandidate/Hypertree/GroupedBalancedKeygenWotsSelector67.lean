import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsIndex67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsPrepared67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67. -/
section
/-! The first WOTS leaf header and tree address are assembled from keygen controls. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsPrepared67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHeader67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsIndex67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

theorem all_pc (s : MachineState) (pc : s.pc = 0x1234) :
    (allState s).pc = 0x127c := by
  change (index2State (index1State (index0State s))).pc = 0x127c
  rw [index2_pc _ (index1_pc _ (index0_pc s pc))]

theorem all_mem (s : MachineState) (a : Word) :
    (allState s).getMem a =
      if a = 0x80018 then s.getMem 0x81018 else
      if a = 0x80010 then s.getMem 0x81010 else
      if a = 0x80008 then s.getMem 0x81008 else s.getMem a := by
  simp only [allState,GroupedBalancedKeygenFirstHashMemory67.index2_mem,
    GroupedBalancedKeygenFirstHashMemory67.index1_mem,
    GroupedBalancedKeygenFirstHashMemory67.index0_mem]
  split_ifs <;> simp_all

def wotsState (s : MachineState) : MachineState :=
  allState (GroupedBalancedKeygenWotsHeader67.headerState (resetState s))

theorem wots_steps (s : MachineState) (pc : s.pc = 0x11d8) :
    OrdinarySteps image s 41 (wotsState s) := by
  obtain ⟨resetPC,_,_⟩ := reset_fields s pc
  obtain ⟨headerPC,_⟩ := header_fields (resetState s) resetPC
  have first := reset_steps s pc
  have second := header_steps (resetState s) resetPC
  have third := all_steps (GroupedBalancedKeygenWotsHeader67.headerState (resetState s)) headerPC
  have pre := Keygen.ordinary_trans image s (resetState s)
    (GroupedBalancedKeygenWotsHeader67.headerState (resetState s)) 4 19 first second
  simpa only [wotsState,image,GroupedBalancedKeygenWotsHeader67.image,
    GroupedBalancedKeygenWotsIndex67.image,Nat.reduceAdd] using
      Keygen.ordinary_trans image s (GroupedBalancedKeygenWotsHeader67.headerState (resetState s))
        (wotsState s) 23 18 pre third

theorem wots_pc (s : MachineState) (pc : s.pc = 0x11d8) :
    (wotsState s).pc = 0x127c := by
  obtain ⟨resetPC,_,_⟩ := reset_fields s pc
  obtain ⟨headerPC,_⟩ := header_fields (resetState s) resetPC
  exact all_pc _ headerPC

theorem wots_header (s : MachineState) (pc : s.pc = 0x11d8) :
    (wotsState s).getMem 0x80000 =
      2 + (s.getMem 0x81000 <<< 8) + (s.getMem 0x81030 <<< 24) := by
  obtain ⟨resetPC,resetChain,_⟩ := reset_fields s pc
  obtain ⟨_,headerWord⟩ := header_fields (resetState s) resetPC
  change (allState (GroupedBalancedKeygenWotsHeader67.headerState (resetState s))).getMem 0x80000 = _
  rw [all_mem]
  rw [headerWord,reset_mem_other s 0x81000 (by decide),
    reset_mem_other s 0x81030 (by decide),resetChain]
  simp

theorem wots_index (s : MachineState) (i : Fin 3) :
    (wotsState s).getMem (Signing.wordAddress 0x80008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  fin_cases i <;>
    simp [wotsState,all_mem,Signing.wordAddress,
      header_mem_other,reset_mem_other]

#print axioms wots_steps
#print axioms wots_header

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsPrepared67

end

/-! The first top-tree leaf uses three WOTS chain hashes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedKeygenImage67.image

def selectorState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 3)
  let s := execInstrBr s (.ADDI .x10 .x0 65)
  let s := execInstrBr s (.BEQ .x19 .x10 16)
  let s := execInstrBr s (.ADDI .x10 .x0 66)
  let s := execInstrBr s (.BEQ .x19 .x10 16)
  let s := execInstrBr s (.JAL .x0 16)
  let s := execInstrBr s (.ADD .x20 .x7 .x0)
  execInstrBr s (.ADDI .x21 .x0 0)

private theorem selector_code :
    Keygen.instructionAt image 0x127c = some (.base (.ADDI .x7 .x0 3)) ∧
    Keygen.instructionAt image 0x1280 = some (.base (.ADDI .x10 .x0 65)) ∧
    Keygen.instructionAt image 0x1284 = some (.base (.BEQ .x19 .x10 16)) ∧
    Keygen.instructionAt image 0x1288 = some (.base (.ADDI .x10 .x0 66)) ∧
    Keygen.instructionAt image 0x128c = some (.base (.BEQ .x19 .x10 16)) ∧
    Keygen.instructionAt image 0x1290 = some (.base (.JAL .x0 16)) ∧
    Keygen.instructionAt image 0x12a0 = some (.base (.ADD .x20 .x7 .x0)) ∧
    Keygen.instructionAt image 0x12a4 = some (.base (.ADDI .x21 .x0 0)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem selector_steps (s : MachineState) (pc : s.pc = 0x127c)
    (leaf : s.getReg .x19 = 0) :
    OrdinarySteps image s 8 (selectorState s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 3)
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 65)
  let s3 := execInstrBr s2 (.BEQ .x19 .x10 16)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 66)
  let s5 := execInstrBr s4 (.BEQ .x19 .x10 16)
  let s6 := execInstrBr s5 (.JAL .x0 16)
  let s7 := execInstrBr s6 (.ADD .x20 .x7 .x0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := selector_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 3)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x0 65)) 6
  · have hp : s1.pc = 0x1280 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x19 .x10 16)) 5
  · have hp : s2.pc = 0x1284 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 66)) 4
  · have hp : s3.pc = 0x1288 := by
      simp [s1,s2,s3,execInstrBr,pc,leaf,signExtend12,signExtend13,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.BEQ .x19 .x10 16)) 3
  · have hp : s4.pc = 0x128c := by
      simp [s1,s2,s3,s4,execInstrBr,pc,leaf,signExtend12,signExtend13,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 16)) 2
  · have hp : s5.pc = 0x1290 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,leaf,signExtend12,signExtend13,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x20 .x7 .x0)) 1
  · have hp : s6.pc = 0x12a0 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,leaf,signExtend12,signExtend13,signExtend21,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (selectorState s) _ (.base (.ADDI .x21 .x0 0)) 0
  · have hp : s7.pc = 0x12a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,leaf,signExtend12,signExtend13,signExtend21,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem selector_fields (s : MachineState) (pc : s.pc = 0x127c)
    (leaf : s.getReg .x19 = 0) :
    (selectorState s).pc = 0x12a8 ∧
    (selectorState s).getReg .x20 = 3 ∧
    (selectorState s).getReg .x21 = 0 ∧
    (selectorState s).getReg .x19 = 0 := by
  simp [selectorState,execInstrBr,signExtend12,signExtend13,signExtend21,
    pc,leaf,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem selector_mem (s : MachineState) (a : Word) :
    (selectorState s).getMem a = s.getMem a := by
  simp [selectorState,execInstrBr]

#print axioms selector_steps
#print axioms selector_fields

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67
