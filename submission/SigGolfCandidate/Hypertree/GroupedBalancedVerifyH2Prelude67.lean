import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Output67

/-! Read the H5 index and first witness sibling before the verifier's H2 query. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Prelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def preludeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x310)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x6 .x6 32)
  let s := execInstrBr s (.SRLI .x6 .x6 32)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x18)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x510)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)

private theorem prelude_code :
    Keygen.instructionAt image 0x1140 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1144 = some (.base (.ADDI .x28 .x28 0x310)) ∧
    Keygen.instructionAt image 0x1148 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x114c = some (.base (.SLLI .x6 .x6 32)) ∧
    Keygen.instructionAt image 0x1150 = some (.base (.SRLI .x6 .x6 32)) ∧
    Keygen.instructionAt image 0x1154 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1158 = some (.base (.ADDI .x28 .x28 0x18)) ∧
    Keygen.instructionAt image 0x115c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1160 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1164 = some (.base (.ADDI .x28 .x28 0x48)) ∧
    Keygen.instructionAt image 0x1168 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x116c = some (.base (.LD .x10 .x7 0)) ∧
    Keygen.instructionAt image 0x1170 = some (.base (.LD .x11 .x7 8)) ∧
    Keygen.instructionAt image 0x1174 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1178 = some (.base (.ADDI .x7 .x7 0x510)) ∧
    Keygen.instructionAt image 0x117c = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1180 = some (.base (.SD .x7 .x11 8))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem prelude_steps (s : MachineState) (pc : s.pc = 0x1140)
    (pointer : s.getMem 0x81048 = 0x2c720) :
    OrdinarySteps image s 17 (preludeState s) := by
  have pointerBV : s.getMem 0x81048#64 = 0x2c720#64 := by simpa using pointer
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x310)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 32)
  let s5 := execInstrBr s4 (.SRLI .x6 .x6 32)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x18)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.LUI .x28 0x81)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0x48)
  let s11 := execInstrBr s10 (.LD .x7 .x28 0)
  let s12 := execInstrBr s11 (.LD .x10 .x7 0)
  let s13 := execInstrBr s12 (.LD .x11 .x7 8)
  let s14 := execInstrBr s13 (.LUI .x7 0x80)
  let s15 := execInstrBr s14 (.ADDI .x7 .x7 0x510)
  let s16 := execInstrBr s15 (.SD .x7 .x10 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16⟩ := prelude_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 16
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x310)) 15
  · have hp : s1.pc = 0x1144 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 14
  · have hp : s2.pc = 0x1148 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 32)) 13
  · have hp : s3.pc = 0x114c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x6 .x6 32)) 12
  · have hp : s4.pc = 0x1150 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s5.pc = 0x1154 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x18)) 10
  · have hp : s6.pc = 0x1158 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s7.pc = 0x115c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s8.pc = 0x1160 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0x48)) 7
  · have hp : s9.pc = 0x1164 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x7 .x28 0)) 6
  · have hp : s10.pc = 0x1168 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x10 .x7 0)) 5
  · have hp : s11.pc = 0x116c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x11 .x7 8)) 4
  · have hp : s12.pc = 0x1170 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x7 0x80)) 3
  · have hp : s13.pc = 0x1174 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x7 .x7 0x510)) 2
  · have hp : s14.pc = 0x1178 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x7 .x10 0)) 1
  · have hp : s15.pc = 0x117c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s16 (preludeState s) _ (.base (.SD .x7 .x11 8)) 0
  · have hp : s16.pc = 0x1180 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [preludeState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,pointerBV,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  exact OrdinarySteps.refl _

theorem prelude_pc (s : MachineState) (pc : s.pc = 0x1140) :
    (preludeState s).pc = 0x1184 := by
  simp [preludeState,execInstrBr,pc]

theorem prelude_sibling (s : MachineState)
    (pointer : s.getMem 0x81048 = 0x2c720) :
    (preludeState s).getMem 0x80510 = s.getMem 0x2c720 ∧
    (preludeState s).getMem 0x80518 = s.getMem 0x2c728 ∧
    (preludeState s).getMem 0x81048 = 0x2c720 := by
  have pointerBV : s.getMem 0x81048#64 = 0x2c720#64 := by simpa using pointer
  simp [preludeState,execInstrBr,signExtend12,pointerBV,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem loaded_prelude (hash : Hash)
    (input : Input GroupedBalancedProgram67Byte.submission.sizes .verify) :
    ∃ (initial before final : MachineState),
      initialState GroupedBalancedProgram67Byte.submission .verify input = some initial ∧
      Trace hash image initial 139 154 1 2 final ∧ final.pc = 0x1184 ∧
      final.getMem 0x80510 = before.getMem 0x2c720 ∧
      final.getMem 0x80518 = before.getMem 0x2c728 ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,_,before,loaded,beforeTrace,beforePC,_,pointer⟩ :=
    GroupedBalancedVerifyH5Output67.loaded_output hash input
  have preludeRun := prelude_steps before beforePC pointer
  obtain ⟨low,high,ptr⟩ := prelude_sibling before pointer
  refine ⟨initial,before,preludeState before,loaded,?_,prelude_pc before beforePC,
    low,high,ptr⟩
  simpa only [Nat.reduceAdd] using beforeTrace.trans preludeRun.trace

#print axioms prelude_steps
#print axioms loaded_prelude
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Prelude67
