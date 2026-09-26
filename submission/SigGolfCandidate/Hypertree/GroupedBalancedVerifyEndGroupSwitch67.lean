import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupLoop67

/-! At group 30 the verifier switches from height three to height four. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyEndGroup67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def switchState (s : MachineState) : MachineState :=
  let s := countState s
  let s := execInstrBr s (.BEQ .x6 .x7 8)
  let s := execInstrBr s (.ADDI .x6 .x0 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 45)
  execInstrBr s (.BNE .x6 .x7 (-1260))

private theorem switch_code :
    Keygen.instructionAt image 0x19e4 =
      some (.base (.BEQ .x6 .x7 8)) ∧
    Keygen.instructionAt image 0x19ec =
      some (.base (.ADDI .x6 .x0 4)) ∧
    Keygen.instructionAt image 0x19f0 =
      some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19f4 =
      some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x19f8 =
      some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x19fc =
      some (.base (.ADDI .x7 .x0 45)) ∧
    Keygen.instructionAt image 0x1a00 =
      some (.base (.BNE .x6 .x7 (-1260))) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem switch_steps (s : MachineState)
    (pc : s.pc = 0x19c4) (group : s.getMem 0x81058 = 29) :
    OrdinarySteps image (countState s) 7 (switchState s) := by
  let s1 := execInstrBr (countState s) (.BEQ .x6 .x7 8)
  let s2 := execInstrBr s1 (.ADDI .x6 .x0 4)
  let s3 := execInstrBr s2 (.LUI .x28 0x81)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0x60)
  let s5 := execInstrBr s4 (.SD .x28 .x6 0)
  let s6 := execInstrBr s5 (.ADDI .x7 .x0 45)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := switch_code
  have x6 : (countState s).getReg .x6 = 30 := by
    rw [count_x6,group]
    decide
  have x7 : (countState s).getReg .x7 = 30 := count_x7 s
  have pc0 : (countState s).pc = 0x19e4 := count_pc s pc
  have pc1 : s1.pc = 0x19ec := by
    simp [s1,execInstrBr,pc0,x6,x7,signExtend13]
  have pc2 : s2.pc = 0x19f0 := by
    simp [s2,execInstrBr,pc1]
  have pc3 : s3.pc = 0x19f4 := by
    simp [s3,execInstrBr,pc2]
  have pc4 : s4.pc = 0x19f8 := by
    simp [s4,execInstrBr,pc3]
  have pc5 : s5.pc = 0x19fc := by
    simp [s5,execInstrBr,pc4]
  have pc6 : s6.pc = 0x1a00 := by
    simp [s6,execInstrBr,pc5]
  apply OrdinarySteps.step (countState s) s1 _
      (.base (.BEQ .x6 .x7 8)) 6
  · simpa only [Keygen.fetch_at,pc0] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _
      (.base (.ADDI .x6 .x0 4)) 5
  · simpa only [Keygen.fetch_at,pc1] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _
      (.base (.LUI .x28 0x81)) 4
  · simpa only [Keygen.fetch_at,pc2] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _
      (.base (.ADDI .x28 .x28 0x60)) 3
  · simpa only [Keygen.fetch_at,pc3] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _
      (.base (.SD .x28 .x6 0)) 2
  · simpa only [Keygen.fetch_at,pc4] using c4
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _
      (.base (.ADDI .x7 .x0 45)) 1
  · simpa only [Keygen.fetch_at,pc5] using c5
  · rfl
  apply OrdinarySteps.step s6 (switchState s) _
      (.base (.BNE .x6 .x7 (-1260))) 0
  · simpa only [Keygen.fetch_at,pc6] using c6
  · rfl
  exact OrdinarySteps.refl _

#print axioms switch_steps
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupSwitch67
