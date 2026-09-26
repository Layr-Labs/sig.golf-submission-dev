import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Fold67

/-! Reset the decoder controls and call the byte-table decoder. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePost67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def postState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 3)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  execInstrBr s (.SD .x28 .x6 0)

private theorem post_code :
    Keygen.instructionAt image 0x14f4 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x14f8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14fc = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x1500 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1504 = some (.base (.ADDI .x6 .x0 3)) ∧
    Keygen.instructionAt image 0x1508 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x150c = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x1510 = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem post_steps (s : MachineState) (pc : s.pc = 0x14f4) :
    OrdinarySteps image s 8 (postState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x58)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 3)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x60)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := post_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s1.pc = 0x14f8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x58)) 5
  · have hp : s2.pc = 0x14fc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s3.pc = 0x1500 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 3)) 3
  · have hp : s4.pc = 0x1504 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s5.pc = 0x1508 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x60)) 1
  · have hp : s6.pc = 0x150c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (postState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s7.pc = 0x1510 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [postState,s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem post_pc (s : MachineState) (pc : s.pc = 0x14f4) :
    (postState s).pc = 0x1514 := by
  simp [postState,execInstrBr,pc]

theorem post_controls (s : MachineState) :
    (postState s).getMem 0x81058 = 0 ∧
    (postState s).getMem 0x81060 = 3 := by
  simp [postState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem post_mem (s : MachineState) (a : Word)
    (h58 : a ≠ 0x81058) (h60 : a ≠ 0x81060) :
    (postState s).getMem a = s.getMem a := by
  simp [postState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  split_ifs with e1 e2
  · exact False.elim (h60 e1)
  · exact False.elim (h58 e2)
  · rfl

theorem post_stack (s : MachineState) :
    (postState s).getReg .x2 = s.getReg .x2 := by
  simp [postState,execInstrBr,MachineState.getReg_setReg_ne]

private theorem call_code :
    Keygen.instructionAt image 0x1514 = some (.base (.JAL .x1 0x538)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

def callState (s : MachineState) : MachineState := execInstrBr s (.JAL .x1 0x538)

theorem call_step (s : MachineState) (pc : s.pc = 0x1514) :
    OrdinarySteps image s 1 (callState s) := by
  apply OrdinarySteps.step s (callState s) _ (.base (.JAL .x1 0x538)) 0
  · simpa only [Keygen.fetch_at,pc] using call_code
  · rfl
  exact OrdinarySteps.refl _

theorem call_pc (s : MachineState) (pc : s.pc = 0x1514) :
    (callState s).pc = 0x1a4c := by
  simp [callState,execInstrBr,pc,signExtend21]

theorem call_link (s : MachineState) (pc : s.pc = 0x1514) :
    (callState s).getReg .x1 = 0x1518 := by
  simp [callState,execInstrBr,pc,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem call_mem (s : MachineState) (a : Word) :
    (callState s).getMem a = s.getMem a := by
  simp [callState,execInstrBr]

private abbrev program := GroupedBalancedProgram67Byte.submission

theorem loaded_call (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n called,
      initialState program .verify input = some initial ∧
      n ≤ 1857 ∧
      Trace hash image initial n (n+92) 12 13 called ∧
      called.pc = 0x1a4c ∧ called.getReg .x1 = 0x1518 ∧
      called.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt 10 ∧
      called.getMem 0x81058 = 0 ∧ called.getMem 0x81060 = 3 := by
  obtain ⟨initial,n,tree,loaded,nbound,treeRun,treePC,pointer,_⟩ :=
    GroupedBalancedVerifyTreeH4Fold67.loaded_tree hash input
  let post := postState tree
  let called := callState post
  have postRun := post_steps tree treePC
  have postPC := post_pc tree treePC
  have callRun := call_step post postPC
  obtain ⟨ctrl58,ctrl60⟩ := post_controls tree
  refine ⟨initial,n+9,called,loaded,by omega,?_,call_pc post postPC,
    call_link post postPC,?_,?_,?_⟩
  · have run := (treeRun.trans postRun.trace).trans callRun.trace
    simpa [image,called,post,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run
  · rw [call_mem,post_mem tree 0x81048 (by decide) (by decide),pointer]
  · rw [call_mem,ctrl58]
  · rw [call_mem,ctrl60]

#print axioms post_steps
#print axioms call_step
#print axioms loaded_call
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePost67
