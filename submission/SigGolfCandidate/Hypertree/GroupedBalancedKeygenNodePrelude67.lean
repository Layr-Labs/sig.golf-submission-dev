import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeavesFold67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeSetup67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodePrelude67. -/
section
/-! Set up the four-level direct67 keygen H4 tree. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeSetup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 8)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 112)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 130)
  let s := execInstrBr s (.ADDI .x6 .x6 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 120)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 130)
  let s := execInstrBr s (.ADDI .x6 .x6 256)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 128)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 64)
  execInstrBr s (.SD .x28 .x6 0)
private theorem setup_code :
    Keygen.instructionAt image 0x1428 = some (.base (.ADDI .x6 .x0 8)) ∧
    Keygen.instructionAt image 0x142c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1430 = some (.base (.ADDI .x28 .x28 112)) ∧
    Keygen.instructionAt image 0x1434 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1438 = some (.base (.LUI .x6 130)) ∧
    Keygen.instructionAt image 0x143c = some (.base (.ADDI .x6 .x6 0)) ∧
    Keygen.instructionAt image 0x1440 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1444 = some (.base (.ADDI .x28 .x28 120)) ∧
    Keygen.instructionAt image 0x1448 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x144c = some (.base (.LUI .x6 130)) ∧
    Keygen.instructionAt image 0x1450 = some (.base (.ADDI .x6 .x6 256)) ∧
    Keygen.instructionAt image 0x1454 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1458 = some (.base (.ADDI .x28 .x28 128)) ∧
    Keygen.instructionAt image 0x145c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1460 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1464 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1468 = some (.base (.ADDI .x28 .x28 80)) ∧
    Keygen.instructionAt image 0x146c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1470 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1474 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1478 = some (.base (.ADDI .x28 .x28 64)) ∧
    Keygen.instructionAt image 0x147c = some (.base (.SD .x28 .x6 0))
    := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem setup_steps (s : MachineState) (pc : s.pc = 0x1428) :
    OrdinarySteps image s 22 (setupState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 8)
  let s2 := execInstrBr s1 (.LUI .x28 129)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 112)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.LUI .x6 130)
  let s6 := execInstrBr s5 (.ADDI .x6 .x6 0)
  let s7 := execInstrBr s6 (.LUI .x28 129)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 120)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  let s10 := execInstrBr s9 (.LUI .x6 130)
  let s11 := execInstrBr s10 (.ADDI .x6 .x6 256)
  let s12 := execInstrBr s11 (.LUI .x28 129)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 128)
  let s14 := execInstrBr s13 (.SD .x28 .x6 0)
  let s15 := execInstrBr s14 (.ADDI .x6 .x0 0)
  let s16 := execInstrBr s15 (.LUI .x28 129)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 80)
  let s18 := execInstrBr s17 (.SD .x28 .x6 0)
  let s19 := execInstrBr s18 (.ADDI .x6 .x0 0)
  let s20 := execInstrBr s19 (.LUI .x28 129)
  let s21 := execInstrBr s20 (.ADDI .x28 .x28 64)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 8)) 21
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 129)) 20
  · have hp : s1.pc = 0x142c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 112)) 19
  · have hp : s2.pc = 0x1430 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 18
  · have hp : s3.pc = 0x1434 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,setupState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x6 130)) 17
  · have hp : s4.pc = 0x1438 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x6 0)) 16
  · have hp : s5.pc = 0x143c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 129)) 15
  · have hp : s6.pc = 0x1440 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 120)) 14
  · have hp : s7.pc = 0x1444 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 13
  · have hp : s8.pc = 0x1448 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,setupState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x6 130)) 12
  · have hp : s9.pc = 0x144c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x6 .x6 256)) 11
  · have hp : s10.pc = 0x1450 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 129)) 10
  · have hp : s11.pc = 0x1454 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 128)) 9
  · have hp : s12.pc = 0x1458 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x6 0)) 8
  · have hp : s13.pc = 0x145c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,setupState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x6 .x0 0)) 7
  · have hp : s14.pc = 0x1460 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 129)) 6
  · have hp : s15.pc = 0x1464 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 80)) 5
  · have hp : s16.pc = 0x1468 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s17.pc = 0x146c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,setupState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s18.pc = 0x1470 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.LUI .x28 129)) 2
  · have hp : s19.pc = 0x1474 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x28 .x28 64)) 1
  · have hp : s20.pc = 0x1478 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 (setupState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s21.pc = 0x147c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,setupState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem setup_pc (s : MachineState) (pc : s.pc = 0x1428) :
    (setupState s).pc = 0x1480 := by
  simp [setupState,execInstrBr,pc]
theorem setup_fields (s : MachineState) :
    (setupState s).getMem 0x81070 = 8 ∧
    (setupState s).getMem 0x81078 = 0x82000 ∧
    (setupState s).getMem 0x81080 = 0x82100 ∧
    (setupState s).getMem 0x81050 = 0 ∧
    (setupState s).getMem 0x81040 = 0 := by
  simp [setupState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
#print axioms setup_steps
#print axioms setup_fields
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenTreeSetup67

end

/-! Four source words enter the direct67 keygen H4 node buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodePrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def preludeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 64)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.SLLI .x7 .x6 5)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 120)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LD .x11 .x7 0)
  let s := execInstrBr s (.LD .x12 .x7 8)
  let s := execInstrBr s (.LD .x13 .x7 16)
  let s := execInstrBr s (.LD .x14 .x7 24)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.SD .x28 .x12 8)
  let s := execInstrBr s (.SD .x28 .x13 16)
  execInstrBr s (.SD .x28 .x14 24)
private theorem prelude_code :
    Keygen.instructionAt image 0x1480 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1484 = some (.base (.ADDI .x28 .x28 64)) ∧
    Keygen.instructionAt image 0x1488 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x148c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1490 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1494 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1498 = some (.base (.SLLI .x7 .x6 5)) ∧
    Keygen.instructionAt image 0x149c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x14a0 = some (.base (.ADDI .x28 .x28 120)) ∧
    Keygen.instructionAt image 0x14a4 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x14a8 = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x14ac = some (.base (.LD .x11 .x7 0)) ∧
    Keygen.instructionAt image 0x14b0 = some (.base (.LD .x12 .x7 8)) ∧
    Keygen.instructionAt image 0x14b4 = some (.base (.LD .x13 .x7 16)) ∧
    Keygen.instructionAt image 0x14b8 = some (.base (.LD .x14 .x7 24)) ∧
    Keygen.instructionAt image 0x14bc = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x14c0 = some (.base (.ADDI .x28 .x28 32)) ∧
    Keygen.instructionAt image 0x14c4 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x14c8 = some (.base (.SD .x28 .x12 8)) ∧
    Keygen.instructionAt image 0x14cc = some (.base (.SD .x28 .x13 16)) ∧
    Keygen.instructionAt image 0x14d0 = some (.base (.SD .x28 .x14 24))
    := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem prelude_steps (s : MachineState) (pc : s.pc = 0x1480)
    (safe0 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64) 8 = true)
    (safe1 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 8#64) 8 = true)
    (safe2 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 16#64) 8 = true)
    (safe3 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 24#64) 8 = true)
    : OrdinarySteps image s 21 (preludeState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 64)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 129)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x6 0)
  let s7 := execInstrBr s6 (.SLLI .x7 .x6 5)
  let s8 := execInstrBr s7 (.LUI .x28 129)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 120)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.ADD .x7 .x7 .x10)
  let s12 := execInstrBr s11 (.LD .x11 .x7 0)
  let s13 := execInstrBr s12 (.LD .x12 .x7 8)
  let s14 := execInstrBr s13 (.LD .x13 .x7 16)
  let s15 := execInstrBr s14 (.LD .x14 .x7 24)
  let s16 := execInstrBr s15 (.LUI .x28 128)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 32)
  let s18 := execInstrBr s17 (.SD .x28 .x11 0)
  let s19 := execInstrBr s18 (.SD .x28 .x12 8)
  let s20 := execInstrBr s19 (.SD .x28 .x13 16)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20⟩ := prelude_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 20
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 64)) 19
  · have hp : s1.pc = 0x1484 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 18
  · have hp : s2.pc = 0x1488 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 129)) 17
  · have hp : s3.pc = 0x148c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 8)) 16
  · have hp : s4.pc = 0x1490 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x6 0)) 15
  · have hp : s5.pc = 0x1494 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x7 .x6 5)) 14
  · have hp : s6.pc = 0x1498 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 129)) 13
  · have hp : s7.pc = 0x149c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 120)) 12
  · have hp : s8.pc = 0x14a0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 11
  · have hp : s9.pc = 0x14a4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x7 .x7 .x10)) 10
  · have hp : s10.pc = 0x14a8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x7 0)) 9
  · have hp : s11.pc = 0x14ac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,safe2,safe3,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x12 .x7 8)) 8
  · have hp : s12.pc = 0x14b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,safe2,safe3,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.LD .x13 .x7 16)) 7
  · have hp : s13.pc = 0x14b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,safe2,safe3,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x14 .x7 24)) 6
  · have hp : s14.pc = 0x14b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,safe2,safe3,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 128)) 5
  · have hp : s15.pc = 0x14bc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 32)) 4
  · have hp : s16.pc = 0x14c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.SD .x28 .x11 0)) 3
  · have hp : s17.pc = 0x14c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x12 8)) 2
  · have hp : s18.pc = 0x14c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x13 16)) 1
  · have hp : s19.pc = 0x14cc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 (preludeState s) _ (.base (.SD .x28 .x14 24)) 0
  · have hp : s20.pc = 0x14d0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,preludeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem prelude_pc (s : MachineState) (pc : s.pc = 0x1480) :
    (preludeState s).pc = 0x14d4 := by
  simp [preludeState,execInstrBr,pc]
#print axioms prelude_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodePrelude67
