import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStorePtr67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStoreCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def copyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)
theorem copy_steps (s : MachineState) (pc : s.pc = 0x2008)
    (dst0 : accessValid (s.getReg .x7) 8 = true)
    (dst1 : accessValid (s.getReg .x7 + 8) 8 = true) :
    OrdinarySteps image s 2 (copyState s) := by
  let s1 := execInstrBr s (.SD .x7 .x10 0)
  have c0 : Keygen.instructionAt image 0x2008 =
    some (.base (.SD .x7 .x10 0)) := by decide
  have c1 : Keygen.instructionAt image 0x200c =
    some (.base (.SD .x7 .x11 8)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.SD .x7 .x10 0)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · simp [s1,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,dst0]
  apply OrdinarySteps.step s1 (copyState s) _ (.base (.SD .x7 .x11 8)) 0
  · have hp : s1.pc = 0x200c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · simpa [copyState,s1,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne] using dst1
  exact OrdinarySteps.refl _
theorem copy_pc (s : MachineState) (pc : s.pc = 0x2008) :
    (copyState s).pc = 0x2010 := by
  simp [copyState,execInstrBr,pc,signExtend12]
#print axioms copy_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStoreCopy67
