import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHash67
/-! Store one direct67 keygen H4 parent node. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeStore67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def storeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 64)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 128)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 768)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 776)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 64)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 112)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 7880)
private theorem store_code :
    Keygen.instructionAt image 0x155c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1560 = some (.base (.ADDI .x28 .x28 64)) ∧
    Keygen.instructionAt image 0x1564 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1568 = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x156c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1570 = some (.base (.ADDI .x28 .x28 128)) ∧
    Keygen.instructionAt image 0x1574 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x1578 = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x157c = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1580 = some (.base (.ADDI .x28 .x28 768)) ∧
    Keygen.instructionAt image 0x1584 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x1588 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x158c = some (.base (.ADDI .x28 .x28 776)) ∧
    Keygen.instructionAt image 0x1590 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1594 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1598 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x159c = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x15a0 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15a4 = some (.base (.ADDI .x28 .x28 64)) ∧
    Keygen.instructionAt image 0x15a8 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x15ac = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15b0 = some (.base (.ADDI .x28 .x28 112)) ∧
    Keygen.instructionAt image 0x15b4 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x15b8 = some (.base (.BNE .x6 .x7 7880)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem store_steps (s : MachineState) (pc : s.pc = 0x155c)
    (safe0 : accessValid ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64) 8 = true)
    (safe1 : accessValid ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64) 8 = true) :
    OrdinarySteps image s 24 (storeState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 64)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x28 129)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 128)
  let s7 := execInstrBr s6 (.LD .x10 .x28 0)
  let s8 := execInstrBr s7 (.ADD .x7 .x7 .x10)
  let s9 := execInstrBr s8 (.LUI .x28 128)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 768)
  let s11 := execInstrBr s10 (.LD .x10 .x28 0)
  let s12 := execInstrBr s11 (.LUI .x28 128)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 776)
  let s14 := execInstrBr s13 (.LD .x11 .x28 0)
  let s15 := execInstrBr s14 (.SD .x7 .x10 0)
  let s16 := execInstrBr s15 (.SD .x7 .x11 8)
  let s17 := execInstrBr s16 (.ADDI .x6 .x6 1)
  let s18 := execInstrBr s17 (.LUI .x28 129)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 64)
  let s20 := execInstrBr s19 (.SD .x28 .x6 0)
  let s21 := execInstrBr s20 (.LUI .x28 129)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 112)
  let s23 := execInstrBr s22 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23⟩ := store_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 23
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 64)) 22
  · have hp : s1.pc = 0x1560 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 21
  · have hp : s2.pc = 0x1564 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 20
  · have hp : s3.pc = 0x1568 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 129)) 19
  · have hp : s4.pc = 0x156c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 128)) 18
  · have hp : s5.pc = 0x1570 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x10 .x28 0)) 17
  · have hp : s6.pc = 0x1574 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x7 .x7 .x10)) 16
  · have hp : s7.pc = 0x1578 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 128)) 15
  · have hp : s8.pc = 0x157c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 768)) 14
  · have hp : s9.pc = 0x1580 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x10 .x28 0)) 13
  · have hp : s10.pc = 0x1584 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 128)) 12
  · have hp : s11.pc = 0x1588 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 776)) 11
  · have hp : s12.pc = 0x158c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s13.pc = 0x1590 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x7 .x10 0)) 9
  · have hp : s14.pc = 0x1594 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x7 .x11 8)) 8
  · have hp : s15.pc = 0x1598 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe0,safe1,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x6 .x6 1)) 7
  · have hp : s16.pc = 0x159c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 129)) 6
  · have hp : s17.pc = 0x15a0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 64)) 5
  · have hp : s18.pc = 0x15a4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s19.pc = 0x15a8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 129)) 3
  · have hp : s20.pc = 0x15ac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 112)) 2
  · have hp : s21.pc = 0x15b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x7 .x28 0)) 1
  · have hp : s22.pc = 0x15b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s23 (storeState s) _ (.base (.BNE .x6 .x7 7880)) 0
  · have hp : s23.pc = 0x15b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  exact OrdinarySteps.refl _

theorem store_pc (s : MachineState) (pc : s.pc = 0x155c)
    (far0 : 0x81070#64 ≠ (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64)
    (far1 : 0x81070#64 ≠ (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64) :
    (storeState s).pc =
      if s.getMem 0x81040#64 + 1 = s.getMem 0x81070#64 then 0x15bc else 0x1480 := by
  simp [storeState,execInstrBr,signExtend12,signExtend13,far0,far1,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem store_counter (s : MachineState) :
    (storeState s).getMem 0x81040#64 = s.getMem 0x81040#64 + 1 := by
  simp [storeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem store_mem (s : MachineState) (a : Word) :
    (storeState s).getMem a =
      if a = 0x81040#64 then s.getMem 0x81040#64 + 1 else
      if a = (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64 then
        s.getMem 0x80308#64 else
      if a = (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 then
        s.getMem 0x80300#64 else s.getMem a := by
  simp [storeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem store_below_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x82000) (notCounter : a ≠ 0x81040#64)
    (destLow : 0x82000 ≤ ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64).toNat)
    (destNextLow : 0x82000 ≤ ((s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64).toNat) :
    (storeState s).getMem a = s.getMem a := by
  rw [store_mem,if_neg notCounter]
  have h0 : a ≠ (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq; omega
  have h1 : a ≠ (s.getMem 0x81040#64 <<< 4) + s.getMem 0x81080#64 + 8#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq; omega
  simp [h0,h1]

#print axioms store_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeStore67
