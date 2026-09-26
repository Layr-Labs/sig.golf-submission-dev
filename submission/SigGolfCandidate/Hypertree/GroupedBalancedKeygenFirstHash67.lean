import SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretCopy67
import SigGolfCandidate.Hypertree.KeygenDomain
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def image : Image := GroupedBalancedKeygenImage67.image
def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  s

def index0State (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  s

def index1State (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  s

def index2State (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  s

def regsState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 512)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  s

def preHashState (s : MachineState) : MachineState :=
  regsState (index2State (index1State (index0State (headerState s))))
private theorem pre_hash_code :
    Keygen.instructionAt image 4256 = some (.base (.ADDI .x10 .x0 1)) ∧
    Keygen.instructionAt image 4260 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4264 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 4268 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4272 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 4276 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 4280 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4284 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 4288 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4292 = some (.base (.SLLI .x11 .x11 24)) ∧
    Keygen.instructionAt image 4296 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 4300 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4304 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 4308 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 4312 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4316 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 4320 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4324 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4328 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 4332 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 4336 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4340 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 4344 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4348 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4352 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 4356 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 4360 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 4364 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 4368 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 4372 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 4376 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 4380 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 4384 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 4388 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 4392 = some (.base (.ADDI .x11 .x0 512)) ∧
    Keygen.instructionAt image 4396 = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 4400 = some (.base (.ADDI .x12 .x12 0x300)) ∧
    Keygen.instructionAt image 4404 = some (.base (.ADDI .x5 .x0 1)) :=
  by unfold image GroupedBalancedKeygenImage67.image; decide
theorem pre_hash_steps_any (s : MachineState) (pc : s.pc = 0x10a0)
    (level : s.getMem 0x81000 = 156) :
    OrdinarySteps image s 38 (preHashState s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37⟩ := pre_hash_code
  let s1 := execInstrBr s (.ADDI .x10 .x0 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 48)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.SLLI .x11 .x11 24)
  let s11 := execInstrBr s10 (.ADD .x10 .x10 .x11)
  let s12 := execInstrBr s11 (.LUI .x28 0x80)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0)
  let s14 := execInstrBr s13 (.SD .x28 .x10 0)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 8)
  let s17 := execInstrBr s16 (.LD .x11 .x28 0)
  let s18 := execInstrBr s17 (.LUI .x28 0x80)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 8)
  let s20 := execInstrBr s19 (.SD .x28 .x11 0)
  let s21 := execInstrBr s20 (.LUI .x28 0x81)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 16)
  let s23 := execInstrBr s22 (.LD .x11 .x28 0)
  let s24 := execInstrBr s23 (.LUI .x28 0x80)
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 16)
  let s26 := execInstrBr s25 (.SD .x28 .x11 0)
  let s27 := execInstrBr s26 (.LUI .x28 0x81)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.LD .x11 .x28 0)
  let s30 := execInstrBr s29 (.LUI .x28 0x80)
  let s31 := execInstrBr s30 (.ADDI .x28 .x28 24)
  let s32 := execInstrBr s31 (.SD .x28 .x11 0)
  let s33 := execInstrBr s32 (.LUI .x10 0x80)
  let s34 := execInstrBr s33 (.ADDI .x10 .x10 0)
  let s35 := execInstrBr s34 (.ADDI .x11 .x0 512)
  let s36 := execInstrBr s35 (.LUI .x12 0x80)
  let s37 := execInstrBr s36 (.ADDI .x12 .x12 0x300)
  let s38 := execInstrBr s37 (.ADDI .x5 .x0 1)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 1)) 37
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 36
  · have hp : s1.pc = 4260 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 35
  · have hp : s2.pc = 4264 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 34
  · have hp : s3.pc = 4268 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 33
  · have hp : s4.pc = 4272 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 32
  · have hp : s5.pc = 4276 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 31
  · have hp : s6.pc = 4280 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 48)) 30
  · have hp : s7.pc = 4284 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 29
  · have hp : s8.pc = 4288 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 24)) 28
  · have hp : s9.pc = 4292 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 27
  · have hp : s10.pc = 4296 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x80)) 26
  · have hp : s11.pc = 4300 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0)) 25
  · have hp : s12.pc = 4304 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x10 0)) 24
  · have hp : s13.pc = 4308 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 23
  · have hp : s14.pc = 4312 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 8)) 22
  · have hp : s15.pc = 4316 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LD .x11 .x28 0)) 21
  · have hp : s16.pc = 4320 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x80)) 20
  · have hp : s17.pc = 4324 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s18.pc = 4328 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x11 0)) 18
  · have hp : s19.pc = 4332 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s20.pc = 4336 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 16)) 16
  · have hp : s21.pc = 4340 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s22.pc = 4344 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s23 s24 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s23.pc = 4348 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s24.pc = 4352 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.SD .x28 .x11 0)) 12
  · have hp : s25.pc = 4356 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s26.pc = 4360 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 24)) 10
  · have hp : s27.pc = 4364 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s28.pc = 4368 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s29.pc = 4372 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s30.pc = 4376 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s31.pc = 4380 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,preHashState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,level]
  apply OrdinarySteps.step s32 s33 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s32.pc = 4384 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  apply OrdinarySteps.step s33 s34 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s33.pc = 4388 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  apply OrdinarySteps.step s34 s35 _ (.base (.ADDI .x11 .x0 512)) 3
  · have hp : s34.pc = 4392 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c34
  · rfl
  apply OrdinarySteps.step s35 s36 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s35.pc = 4396 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c35
  · rfl
  apply OrdinarySteps.step s36 s37 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s36.pc = 4400 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c36
  · rfl
  apply OrdinarySteps.step s37 (preHashState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s37.pc = 4404 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c37
  · rfl
  exact OrdinarySteps.refl _

theorem pre_hash_steps (s : MachineState) (pc : s.pc = 0x10a0)
    (level : s.getMem 0x81000 = 156) (tree : s.getMem 0x81030 = 0) :
    OrdinarySteps image s 38 (preHashState s) :=
  pre_hash_steps_any s pc level

#print axioms pre_hash_steps_any
#print axioms pre_hash_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHash67
