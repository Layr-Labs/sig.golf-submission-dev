import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomCopies67

/-! Initialize the bottom tree builder before its first leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBuilderInit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def initState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 10)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 1024)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x90)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf8)
  execInstrBr s (.SD .x28 .x6 0)

private theorem init_code :
    Keygen.instructionAt image 0x1278 = some (.base (.ADDI .x6 .x0 10)) ∧
    Keygen.instructionAt image 0x127c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1280 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x1284 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1288 = some (.base (.ADDI .x6 .x0 1024)) ∧
    Keygen.instructionAt image 0x128c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1290 = some (.base (.ADDI .x28 .x28 0xd0)) ∧
    Keygen.instructionAt image 0x1294 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1298 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x129c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12a0 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x12a4 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x12a8 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x12ac = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12b0 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x12b4 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x12b8 = some (.base (.LUI .x6 0x20)) ∧
    Keygen.instructionAt image 0x12bc = some (.base (.ADDI .x6 .x6 0x90)) ∧
    Keygen.instructionAt image 0x12c0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12c4 = some (.base (.ADDI .x28 .x28 0xf8)) ∧
    Keygen.instructionAt image 0x12c8 = some (.base (.SD .x28 .x6 0)) := by
  decide

theorem init_steps (s : MachineState) (pc : s.pc = 0x1278) :
    OrdinarySteps image s 21 (initState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 10)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x60)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 1024)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0xd0)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.ADDI .x6 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0xe0)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  let s13 := execInstrBr s12 (.ADDI .x6 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 0)
  let s16 := execInstrBr s15 (.SD .x28 .x6 0)
  let s17 := execInstrBr s16 (.LUI .x6 0x20)
  let s18 := execInstrBr s17 (.ADDI .x6 .x6 0x90)
  let s19 := execInstrBr s18 (.LUI .x28 0x81)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 0xf8)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20⟩ := init_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 10)) 20
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 19
  · have hp : s1.pc = 0x127c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x60)) 18
  · have hp : s2.pc = 0x1280 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 17
  · have hp : s3.pc = 0x1284 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,initState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 1024)) 16
  · have hp : s4.pc = 0x1288 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 15
  · have hp : s5.pc = 0x128c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0xd0)) 14
  · have hp : s6.pc = 0x1290 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 13
  · have hp : s7.pc = 0x1294 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,initState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x6 .x0 0)) 12
  · have hp : s8.pc = 0x1298 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s9.pc = 0x129c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0xe0)) 10
  · have hp : s10.pc = 0x12a0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s11.pc = 0x12a4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,initState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x6 .x0 0)) 8
  · have hp : s12.pc = 0x12a8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 7
  · have hp : s13.pc = 0x12ac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 0)) 6
  · have hp : s14.pc = 0x12b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x6 0)) 5
  · have hp : s15.pc = 0x12b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,initState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x6 0x20)) 4
  · have hp : s16.pc = 0x12b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x6 .x6 0x90)) 3
  · have hp : s17.pc = 0x12bc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s18.pc = 0x12c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 0xf8)) 1
  · have hp : s19.pc = 0x12c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 (initState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s20.pc = 0x12c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,initState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem init_pc (s : MachineState) (pc : s.pc = 0x1278) :
    (initState s).pc = 0x12cc := by
  simp [initState,execInstrBr,pc]

theorem init_level (s : MachineState) :
    (initState s).getMem 0x81000 = 0x0 := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem init_height (s : MachineState) :
    (initState s).getMem 0x81060 = 0xa := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem init_leaves (s : MachineState) :
    (initState s).getMem 0x810d0 = 0x400 := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem init_counter (s : MachineState) :
    (initState s).getMem 0x810e0 = 0x0 := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem init_pointer (s : MachineState) :
    (initState s).getMem 0x810f8 = 0x20090 := by
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem init_frame (s : MachineState) (a : Word)
    (outside : a ≠ 0x81000 ∧ a ≠ 0x81060 ∧ a ≠ 0x810d0 ∧
      a ≠ 0x810e0 ∧ a ≠ 0x810f8) :
    (initState s).getMem a = s.getMem a := by
  obtain ⟨a0,a1,a2,a3,a4⟩ := outside
  change a ≠ 528384#64 at a0
  change a ≠ 528480#64 at a1
  change a ≠ 528592#64 at a2
  change a ≠ 528608#64 at a3
  change a ≠ 528632#64 at a4
  simp [initState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    a0,a1,a2,a3,a4]

#print axioms init_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBuilderInit67
