import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeBranch67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! Nonzero path bit: current root first, witness sibling second. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeSiblingNonzero67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

private theorem setup_code : Keygen.CopySetupCode image 0x1314 0x500 0x530 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem copy_code : Keygen.CopyCode image 0x1328 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem copy_current (s : MachineState) (pc : s.pc = 0x1314) :
    ∃ mid, OrdinarySteps image s 17 mid ∧ mid.pc = 0x1340 ∧
      (∀ i : Fin 2, mid.getMem (Signing.wordAddress 0x80530 i.val) =
        s.getMem (Signing.wordAddress 0x80500 i.val)) ∧
      mid.getMem 0x81048 = s.getMem 0x81048 ∧
      mid.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s mid := by
  obtain ⟨mid,run,endPC,words,_,sp,frame⟩ :=
    Keygen.copy_two image 0x1314 0x500 0x530 0x80500 0x80530
      setup_code copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  refine ⟨mid,run,by simpa using endPC,words,?_,?_,?_,sp⟩
  · exact frame 0x81048 (by intro i; fin_cases i <;> decide)
  · exact frame 0x81050 (by intro i; fin_cases i <;> decide)
  · intro a ha
    apply frame a
    intro i
    fin_cases i <;> intro eq <;>
      have hn := congrArg BitVec.toNat eq <;>
      simp [Signing.wordAddress] at hn <;> omega

def siblingState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x520)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)

private theorem sibling_code :
    Keygen.instructionAt image 0x1340 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1344 = some (.base (.ADDI .x28 .x28 0x48)) ∧
    Keygen.instructionAt image 0x1348 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x134c = some (.base (.LD .x10 .x7 0)) ∧
    Keygen.instructionAt image 0x1350 = some (.base (.LD .x11 .x7 8)) ∧
    Keygen.instructionAt image 0x1354 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1358 = some (.base (.ADDI .x7 .x7 0x520)) ∧
    Keygen.instructionAt image 0x135c = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1360 = some (.base (.SD .x7 .x11 8))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem sibling_steps (s : MachineState) (p : Word)
    (pc : s.pc = 0x1340) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    OrdinarySteps image s 9 (siblingState s) := by
  have pointerBV : s.getMem 0x81048#64 = p := by simpa using pointer
  have valid8BV : accessValid (p+8#64) 8 = true := by simpa using valid8
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 0x520)
  let s8 := execInstrBr s7 (.SD .x7 .x10 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := sibling_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 8
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 7
  · have hp : s1.pc = 0x1344 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 6
  · have hp : s2.pc = 0x1348 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,valid0,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 5
  · have hp : s3.pc = 0x134c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,pointerBV,valid0,valid8BV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 4
  · have hp : s4.pc = 0x1350 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,pointerBV,valid0,valid8BV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 3
  · have hp : s5.pc = 0x1354 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 0x520)) 2
  · have hp : s6.pc = 0x1358 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x10 0)) 1
  · have hp : s7.pc = 0x135c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,valid0,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s8 (siblingState s) _ (.base (.SD .x7 .x11 8)) 0
  · have hp : s8.pc = 0x1360 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [siblingState,s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,valid0,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  exact OrdinarySteps.refl _

theorem sibling_pc (s : MachineState) (pc : s.pc = 0x1340) :
    (siblingState s).pc = 0x1364 := by
  simp [siblingState,execInstrBr,pc]

theorem sibling_pointer (s : MachineState) :
    (siblingState s).getMem 0x81048 = s.getMem 0x81048 := by
  simp [siblingState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem sibling_count (s : MachineState) :
    (siblingState s).getMem 0x81050 = s.getMem 0x81050 := by
  simp [siblingState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem sibling_safe (s : MachineState) : SafeFrame s (siblingState s) := by
  constructor
  · intro a ha
    have ne0 : a ≠ 0x80520 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp at hn
      omega
    have ne8 : a ≠ 0x80528 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp at hn
      omega
    simp [siblingState,execInstrBr,signExtend12,ne0,ne8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
    split_ifs with h8 h0
    · have hn := congrArg BitVec.toNat h8
      simp at hn
      omega
    · have hn := congrArg BitVec.toNat h0
      simp at hn
      omega
    · rfl
  · simp [siblingState,execInstrBr,MachineState.getReg_setReg_ne]

private theorem jump_code :
    Keygen.instructionAt image 0x1364 = some (.base (.JAL .x0 84)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem jump_step (s : MachineState) (pc : s.pc = 0x1364) :
    OrdinarySteps image s 1 (execInstrBr s (.JAL .x0 84)) := by
  apply OrdinarySteps.step s (execInstrBr s (.JAL .x0 84)) _
    (.base (.JAL .x0 84)) 0
  · simpa only [Keygen.fetch_at,pc] using jump_code
  · rfl
  exact OrdinarySteps.refl _

theorem jump_pc (s : MachineState) (pc : s.pc = 0x1364) :
    (execInstrBr s (.JAL .x0 84)).pc = 0x13b8 := by
  simp [execInstrBr,pc,signExtend21]

theorem nonzero_path (s : MachineState) (p : Word)
    (pc : s.pc = 0x1314) (pointer : s.getMem 0x81048 = p)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ final, OrdinarySteps image s 27 final ∧ final.pc = 0x13b8 ∧
      final.getMem 0x81048 = p ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s final := by
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,copyCount,copySafe⟩ := copy_current s pc
  have copiedPointer : copied.getMem 0x81048 = p := copyPointer.trans pointer
  have siblingRun := sibling_steps copied p copyPC copiedPointer valid0 valid8
  let staged := siblingState copied
  have stagedPC := sibling_pc copied copyPC
  have jumpRun := jump_step staged stagedPC
  refine ⟨execInstrBr staged (.JAL .x0 84),?_,jump_pc staged stagedPC,?_,?_,?_⟩
  · have run := Keygen.ordinary_trans image s copied _ 17 9 copyRun siblingRun
    have all := Keygen.ordinary_trans image s staged _ 26 1
      (by simpa only [Nat.reduceAdd] using run) jumpRun
    simpa only [Nat.reduceAdd] using all
  · simpa [execInstrBr,staged] using
      (sibling_pointer copied).trans copiedPointer
  · simpa [execInstrBr,staged] using
      (sibling_count copied).trans copyCount
  · have jumpSafe : SafeFrame staged (execInstrBr staged (.JAL .x0 84)) := by
      constructor
      · intro a _
        simp [execInstrBr]
      · simp [execInstrBr,MachineState.getReg_setReg_ne]
    exact safe_trans (safe_trans copySafe (sibling_safe copied)) jumpSafe

#print axioms sibling_steps
#print axioms nonzero_path
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeSiblingNonzero67
