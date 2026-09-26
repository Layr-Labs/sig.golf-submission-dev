import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomRootCopy67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperStart67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomToUpper67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

def startState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 3)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x20)
  let s := execInstrBr s (.ADDI .x6 .x6 0x130)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf0)
  execInstrBr s (.SD .x28 .x6 0)

private theorem start_code :
    Keygen.instructionAt image 0x15ac = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x15b0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15b4 = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x15b8 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x15bc = some (.base (.ADDI .x6 .x0 3)) ∧
    Keygen.instructionAt image 0x15c0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15c4 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x15c8 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x15cc = some (.base (.LUI .x6 0x20)) ∧
    Keygen.instructionAt image 0x15d0 = some (.base (.ADDI .x6 .x6 0x130)) ∧
    Keygen.instructionAt image 0x15d4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15d8 = some (.base (.ADDI .x28 .x28 0xf0)) ∧
    Keygen.instructionAt image 0x15dc = some (.base (.SD .x28 .x6 0)) := by decide

theorem start_steps (s : MachineState) (pc : s.pc = 0x15ac) :
    OrdinarySteps image s 13 (startState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x58)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 3)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0x60)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.LUI .x6 0x20)
  let s10 := execInstrBr s9 (.ADDI .x6 .x6 0x130)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0xf0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩ := start_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 12
  · simpa [Keygen.fetch_at, execInstrBr, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 11
  · simpa [Keygen.fetch_at, s1, execInstrBr, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x58)) 10
  · simpa [Keygen.fetch_at, s1, s2, execInstrBr, pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 9
  · simpa [Keygen.fetch_at, s1, s2, s3, execInstrBr, pc] using c3
  · simp [startState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3, s4]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 3)) 8
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, execInstrBr, pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 7
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, execInstrBr, pc] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0x60)) 6
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, execInstrBr, pc] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 5
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc] using c7
  · simp [startState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3, s4, s5, s6, s7, s8]
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x6 0x20)) 4
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x6 0x130)) 3
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0xf0)) 1
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc] using c11
  · rfl
  apply OrdinarySteps.step s12 (startState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc] using c12
  · simp [startState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
  exact OrdinarySteps.refl _

theorem start_pc (s : MachineState) (pc : s.pc = 0x15ac) :
    (startState s).pc = 0x15e0 := by
  simp [startState,execInstrBr,pc]

theorem start_data (s : MachineState) :
    (startState s).getMem 0x81058 = 0 ∧
    (startState s).getMem 0x81060 = 3 ∧
    (startState s).getMem 0x810f0 = 0x20130 := by
  simp [startState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem start_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81058) (h1 : a ≠ 0x81060) (h2 : a ≠ 0x810f0) :
    (startState s).getMem a = s.getMem a := by
  change a ≠ 528472#64 at h0
  change a ≠ 528480#64 at h1
  change a ≠ 528624#64 at h2
  simp [startState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2]

#print axioms start_steps
#print axioms start_data
#print axioms start_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperStart67

end

/-! Exact machine handoff from the bottom Merkle root to the first upper group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomToUpper67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

def Outside (a : Word) : Prop :=
  a ≠ 0x80500 ∧ a ≠ 0x80508 ∧ a ≠ 0x81100 ∧
  a ≠ 0x81090 ∧ a ≠ 0x81098 ∧ a ≠ 0x810a0 ∧
  a ≠ 0x81058 ∧ a ≠ 0x81060 ∧ a ≠ 0x810f0

theorem post_bottom_to_upper (s : MachineState) (index : BitVec 192)
    (pc : s.pc = 0x14f0)
    (source : s.getMem 0x810c0 = 0x83000)
    (selected : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64) :
    ∃ upper : MachineState,
      OrdinarySteps image s 366 upper ∧
      upper.pc = 0x15e0 ∧
      upper.getMem 0x80500 = s.getMem 0x83000 ∧
      upper.getMem 0x80508 = s.getMem 0x83008 ∧
      upper.getMem 0x81058 = 0 ∧
      upper.getMem 0x81060 = 3 ∧
      upper.getMem 0x810f0 = 0x20130 ∧
      (∀ w : Fin 3,
        upper.getMem (Signing.wordAddress 0x81090 w.val) =
          (index >>> 10).extractLsb' (64*w.val) 64) ∧
      (∀ a : Word, Outside a → upper.getMem a = s.getMem a) ∧
      upper.getReg .x2=s.getReg .x2 := by
  let copied := GroupedBalancedSignBottomRootCopy67.copyState s
  have copyTrace := GroupedBalancedSignBottomRootCopy67.copy_steps s pc source
  have copyPc := GroupedBalancedSignBottomRootCopy67.copy_pc s pc
  have copyValues := GroupedBalancedSignBottomRootCopy67.copy_words s source
  have copySelected : ∀ w : Fin 3,
      copied.getMem (Signing.wordAddress 0x81090 w.val) =
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignBottomRootCopy67.copy_frame s _
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)
      (by fin_cases w <;> decide)]
    exact selected w
  have initialFold : GroupedBalancedSignBottomSelectedFold67.Inv index 0 copied := by
    refine ⟨by decide,?_,?_,?_⟩
    · simpa using copyPc
    · simpa using copyValues.2.2
    · simpa using copySelected
  obtain ⟨shifted,shiftTrace,shiftInv,shiftFrame,shiftSp⟩ :=
    GroupedBalancedSignBottomSelectedFold67.run_prefix_frame index copied
      initialFold 10 (by decide)
  let upper := GroupedBalancedSignUpperStart67.startState shifted
  have upperTrace := GroupedBalancedSignUpperStart67.start_steps shifted
    (by simpa [GroupedBalancedSignBottomSelectedFold67.Inv] using shiftInv.2.1)
  have upperPc := GroupedBalancedSignUpperStart67.start_pc shifted
    (by simpa [GroupedBalancedSignBottomSelectedFold67.Inv] using shiftInv.2.1)
  have upperData := GroupedBalancedSignUpperStart67.start_data shifted
  have finalTrace : OrdinarySteps image s 366 upper := by
    simpa [upper,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Keygen.ordinary_trans image s shifted upper 353 13
        (Keygen.ordinary_trans image s copied shifted 13 340 copyTrace
          (by simpa using shiftTrace)) upperTrace
  refine ⟨upper,finalTrace,upperPc,?_,?_,upperData.1,upperData.2.1,
    upperData.2.2,?_,?_,?_⟩
  · rw [GroupedBalancedSignUpperStart67.start_frame shifted 0x80500
      (by decide) (by decide) (by decide),
      shiftFrame 0x80500 (by simp [GroupedBalancedSignBottomSelectedFold67.Outside])]
    exact copyValues.1
  · rw [GroupedBalancedSignUpperStart67.start_frame shifted 0x80508
      (by decide) (by decide) (by decide),
      shiftFrame 0x80508 (by simp [GroupedBalancedSignBottomSelectedFold67.Outside])]
    exact copyValues.2.1
  · intro w
    rw [GroupedBalancedSignUpperStart67.start_frame shifted _
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)
      (by fin_cases w <;> decide)]
    simpa [GroupedBalancedSignBottomSelectedFold67.Inv] using shiftInv.2.2.2 w
  · intro a ha
    rcases ha with ⟨h80500,h80508,h81100,h81090,h81098,h810a0,
      h81058,h81060,h810f0⟩
    rw [GroupedBalancedSignUpperStart67.start_frame shifted a
      h81058 h81060 h810f0,
      shiftFrame a ⟨h81090,h81098,h810a0,h81100⟩,
      GroupedBalancedSignBottomRootCopy67.copy_frame s a
        h80500 h80508 h81100]
  · have copySp : copied.getReg .x2=s.getReg .x2 := by
      simp [copied,GroupedBalancedSignBottomRootCopy67.copyState,
        execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    have startSp : upper.getReg .x2=shifted.getReg .x2 := by
      simp [upper,GroupedBalancedSignUpperStart67.startState,
        execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne]
    exact startSp.trans (shiftSp.trans copySp)

#print axioms post_bottom_to_upper
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomToUpper67
