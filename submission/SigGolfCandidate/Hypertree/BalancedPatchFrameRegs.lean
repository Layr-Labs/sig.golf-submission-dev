import SigGolfCandidate.Hypertree.BalancedPatchWords
import SigGolfCandidate.Hypertree.BalancedPatchExit

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

theorem wordPass_ra (s : MachineState) :
    (wordPass s).getReg .x1 = s.getReg .x1 := by
  simp [wordPass, flipChunk, execInstrBr, MachineState.getReg_setReg_ne]

theorem setup_x10 (s : MachineState) :
    (setupState s).getReg .x10 = s.getReg .x10 := by
  simp [setupState, execInstrBr, MachineState.getReg_setReg_ne]

theorem finish_x10 (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x10 = s.getReg .x10 := by
  simp [finishState, execInstrBr, MachineState.getReg_setReg_ne]

#print axioms wordPass_ra
#print axioms setup_x10
#print axioms finish_x10
end SigGolfCandidate.Hypertree.Signing
