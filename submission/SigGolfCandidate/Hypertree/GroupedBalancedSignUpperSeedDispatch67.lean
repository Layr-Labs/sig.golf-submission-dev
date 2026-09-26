import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Answer67

/-! Select the low or high half of a paired H1 answer from the chain parity. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedDispatch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def dispatchState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ANDI .x6 .x19 1)
  execInstrBr s (.BEQ .x6 .x0 0x34)

private theorem dispatch_code :
    Keygen.instructionAt image 0x1884 = some (.base (.ANDI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x1888 = some (.base (.BEQ .x6 .x0 0x34)) := by decide

theorem dispatch_steps (s : MachineState) (pc : s.pc = 0x1884) :
    OrdinarySteps image s 2 (dispatchState s) := by
  let s1 := execInstrBr s (.ANDI .x6 .x19 1)
  obtain ⟨c0,c1⟩ := dispatch_code
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x6 .x19 1)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 (dispatchState s) _ (.base (.BEQ .x6 .x0 0x34)) 0
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem dispatch_pc (s : MachineState) (pc : s.pc = 0x1884) :
    (dispatchState s).pc =
      if s.getReg .x19 &&& (1 : Word) = 0 then 0x18bc else 0x188c := by
  simp [dispatchState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem dispatch_frame (s : MachineState) (a : Word) :
    (dispatchState s).getMem a = s.getMem a := by
  simp [dispatchState,execInstrBr]

#print axioms dispatch_steps
#print axioms dispatch_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedDispatch67
