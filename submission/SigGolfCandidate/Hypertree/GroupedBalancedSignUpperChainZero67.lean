import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafEntry67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainDispatch67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainZero67. -/
section
/-! WOTS chain dispatch chooses whether a paired-secret H1 query is needed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainDispatch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def dispatchState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  let s := execInstrBr s (.LD .x19 .x28 0)
  let s := execInstrBr s (.ANDI .x6 .x19 1)
  execInstrBr s (.BEQ .x6 .x0 8)

private theorem dispatch_code :
    Keygen.instructionAt image 0x1760 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1764 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x1768 = some (.base (.LD .x19 .x28 0)) ∧
    Keygen.instructionAt image 0x176c = some (.base (.ANDI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x1770 = some (.base (.BEQ .x6 .x0 8)) := by
  decide

theorem dispatch_steps (s : MachineState) (pc : s.pc = 0x1760) :
    OrdinarySteps image s 5 (dispatchState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x30)
  let s3 := execInstrBr s2 (.LD .x19 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x6 .x19 1)
  obtain ⟨c0,c1,c2,c3,c4⟩ := dispatch_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x30)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x19 .x28 0)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x6 .x19 1)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (dispatchState s) _ (.base (.BEQ .x6 .x0 8)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem dispatch_pc (s : MachineState) (pc : s.pc = 0x1760) :
    (dispatchState s).pc =
      if (s.getMem 0x81030 &&& 1#64) = 0 then 0x1778 else 0x1774 := by
  simp [dispatchState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem dispatch_chain (s : MachineState) :
    (dispatchState s).getReg .x19 = s.getMem 0x81030 := by
  simp [dispatchState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem dispatch_frame (s : MachineState) (a : Word) :
    (dispatchState s).getMem a = s.getMem a := by
  simp [dispatchState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms dispatch_steps
#print axioms dispatch_pc
#print axioms dispatch_chain
#print axioms dispatch_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainDispatch67

end

/-! Begin an upper leaf by resetting its 67-chain WOTS counter. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainZero67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def zeroState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  execInstrBr s (.SD .x28 .x6 0)

private theorem zero_code :
    Keygen.instructionAt image 0x1750 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1754 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1758 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x175c = some (.base (.SD .x28 .x6 0)) := by decide

theorem zero_steps (s : MachineState) (pc : s.pc = 0x1750) :
    OrdinarySteps image s 4 (zeroState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x30)
  obtain ⟨c0,c1,c2,c3⟩ := zero_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x30)) 1
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 (zeroState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · have haddr : s3.getReg .x28 = 0x81030 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s3.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (zeroState s) else none) = some (zeroState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem zero_pc (s : MachineState) (pc : s.pc = 0x1750) :
    (zeroState s).pc = 0x1760 := by
  simp [zeroState,execInstrBr,pc]

theorem zero_chain (s : MachineState) :
    (zeroState s).getMem 0x81030 = 0 := by
  simp [zeroState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem zero_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81030) :
    (zeroState s).getMem a = s.getMem a := by
  simp [zeroState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro eq
  exact False.elim (ha eq)

theorem first_pair_entry (s : MachineState) (pc : s.pc = 0x1750) :
    OrdinarySteps image s 9
      (GroupedBalancedSignUpperChainDispatch67.dispatchState (zeroState s)) ∧
    (GroupedBalancedSignUpperChainDispatch67.dispatchState (zeroState s)).pc =
      0x1778 ∧
    (GroupedBalancedSignUpperChainDispatch67.dispatchState (zeroState s)).getReg
      .x19 = 0 := by
  have first := zero_steps s pc
  have pc0 := zero_pc s pc
  have second := GroupedBalancedSignUpperChainDispatch67.dispatch_steps
    (zeroState s) pc0
  refine ⟨?_,?_,?_⟩
  · simpa using GroupedBalancedDecoderByteSumLoop67.steps_comp first second
  · rw [GroupedBalancedSignUpperChainDispatch67.dispatch_pc _ pc0,zero_chain]
    decide
  · rw [GroupedBalancedSignUpperChainDispatch67.dispatch_chain,zero_chain]

#print axioms zero_steps
#print axioms zero_pc
#print axioms zero_chain
#print axioms zero_frame
#print axioms first_pair_entry
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainZero67
