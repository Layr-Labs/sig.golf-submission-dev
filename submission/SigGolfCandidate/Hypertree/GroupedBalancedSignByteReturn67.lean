import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67

/-! The decoder returns to the caller's JAL link register. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteReturn67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCompose67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteTail67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

@[simp] private theorem reg_setByte (s : MachineState) (a : Word)
    (v : BitVec 8) (r : Reg) : (s.setByte a v).getReg r = s.getReg r := by
  simp [MachineState.setByte, MachineState.setMem]
  cases r <;> rfl

@[simp] private theorem reg_setWord32 (s : MachineState) (a : Word)
    (v : BitVec 32) (r : Reg) : (s.setWord32 a v).getReg r = s.getReg r := by
  simp [MachineState.setWord32, MachineState.setMem]
  cases r <;> rfl

private theorem setup_x1 (s : MachineState) :
    (setupState s).getReg .x1 = s.getReg .x1 := by
  simp [setupState, execInstrBr, MachineState.getReg_setReg_ne]

private theorem sumBody_x1 (s : MachineState) :
    (sumBody s).getReg .x1 = s.getReg .x1 := by
  simp [sumBody, execInstrBr, MachineState.getReg_setReg_ne]

private theorem sumLoop_x1 (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x1 = s.getReg .x1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_x1] using ih

private theorem smallBranch_x1 (s : MachineState) :
    (smallBranch s).getReg .x1 = s.getReg .x1 := by
  simp [smallBranch, commonBranch, branchPrefix, execInstrBr,
    MachineState.getReg_setReg_ne]

private theorem largeBranch_x1 (s : MachineState) :
    (largeBranch s).getReg .x1 = s.getReg .x1 := by
  simp [largeBranch, commonBranch, branchPrefix, execInstrBr,
    MachineState.getReg_setReg_ne]

private theorem selectedBranch_x1 (s : MachineState) (message : BitVec 128) :
    (selectedBranch s message).getReg .x1 = s.getReg .x1 := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simpa only [selectedBranch, if_pos h] using smallBranch_x1 s
  · simpa only [selectedBranch, if_neg h] using largeBranch_x1 s

private theorem copyBody_x1 (s : MachineState) :
    (copyBody s).getReg .x1 = s.getReg .x1 := by
  simp [copyBody, execInstrBr, MachineState.getReg_setReg_ne]

private theorem copyLoop_x1 (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x1 = s.getReg .x1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copyLoop, copyBody_x1] using ih

private theorem tail_pc (s : MachineState) (hlink : s.getReg .x1 = 0x1740) :
    (tailState s).pc = 0x1740 := by
  simp [tailState, execInstrBr, MachineState.getReg_setReg_ne,
    hlink, signExtend12]

theorem fullDecoder_return_pc (s : MachineState) (message : BitVec 128)
    (hlink : s.getReg .x1 = 0x1740) :
    (fullDecoderState s message).pc = 0x1740 := by
  have hsetup := setup_x1 s
  have hsum := sumLoop_x1 (setupState s) 16
  have hbranch := selectedBranch_x1 (sumLoop (setupState s) 16) message
  have hcopy := copyLoop_x1
    (selectedBranch (sumLoop (setupState s) 16) message) 16
  apply tail_pc
  rw [hcopy, hbranch, hsum, hsetup]
  exact hlink

#print axioms fullDecoder_return_pc

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteReturn67
