import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Loaded67

/-! Enter the ten-round verifier H4 tree loop after the initial H2 result. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

def startState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 16)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  execInstrBr s (.SD .x28 .x6 0)

private theorem start_code :
    Keygen.instructionAt image 0x1264 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1268 = some (.base (.ADDI .x28 .x28 0x48)) ∧
    Keygen.instructionAt image 0x126c = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1270 = some (.base (.ADDI .x6 .x6 16)) ∧
    Keygen.instructionAt image 0x1274 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1278 = some (.base (.ADDI .x28 .x28 0x48)) ∧
    Keygen.instructionAt image 0x127c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1280 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1284 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1288 = some (.base (.ADDI .x28 .x28 0x50)) ∧
    Keygen.instructionAt image 0x128c = some (.base (.SD .x28 .x6 0))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem start_steps (s : MachineState) (pc : s.pc = 0x1264) :
    OrdinarySteps image s 11 (startState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 16)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x48)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.ADDI .x6 .x0 0)
  let s9 := execInstrBr s8 (.LUI .x28 0x81)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0x50)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := start_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 10
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 9
  · have hp : s1.pc = 0x1268 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s2.pc = 0x126c := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 16)) 7
  · have hp : s3.pc = 0x1270 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s4.pc = 0x1274 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x48)) 5
  · have hp : s5.pc = 0x1278 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s6.pc = 0x127c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s7.pc = 0x1280 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s8.pc = 0x1284 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0x50)) 1
  · have hp : s9.pc = 0x1288 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 (startState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s10.pc = 0x128c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [startState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  exact OrdinarySteps.refl _

theorem start_pc (s : MachineState) (pc : s.pc = 0x1264) :
    (startState s).pc = 0x1290 := by
  simp [startState,execInstrBr,pc]

theorem start_controls (s : MachineState)
    (pointer : s.getMem 0x81048 = 0x2c720) :
    (startState s).getMem 0x81048 = 0x2c730 ∧
    (startState s).getMem 0x81050 = 0 := by
  have pointerBV : s.getMem 0x81048#64 = 0x2c720#64 := by simpa using pointer
  simp [startState,execInstrBr,signExtend12,pointerBV,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem loaded_start (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 218 240 2 3 final ∧ final.pc = 0x1290 ∧
      final.getMem 0x81048 = 0x2c730 ∧ final.getMem 0x81050 = 0 := by
  obtain ⟨initial,_,before,loaded,beforeTrace,beforePC,_,pointer⟩ :=
    GroupedBalancedVerifyH2Loaded67.loaded_output hash input
  have startRun := start_steps before beforePC
  obtain ⟨ptr,count⟩ := start_controls before pointer
  refine ⟨initial,startState before,loaded,?_,start_pc before beforePC,ptr,count⟩
  simpa only [Nat.reduceAdd] using beforeTrace.trans startRun.trace

#print axioms loaded_start
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeStart67
