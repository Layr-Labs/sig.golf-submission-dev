import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Entry67
import SigGolfCandidate.Hypertree.KeygenDomain

/-! Memory fields produced by the verifier's first H2 setup instructions. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Setup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem setup_head (s : MachineState)
    (level : s.getMem 0x81000 = 0) :
    (GroupedBalancedVerifyH2Entry67.setupState s).getMem 0x80000 =
      KeygenDomain.header 2 0 0 0 0 := by
  simp [GroupedBalancedVerifyH2Entry67.setupState,
    KeygenDomain.header,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  have haddr : (BitVec.ofNat 64 528384) = (0x81000 : Word) := by decide
  rw [haddr, level]
  decide

theorem setup_index_words (s : MachineState) :
    ∀ i : Fin 3,
      (GroupedBalancedVerifyH2Entry67.setupState s).getMem
        (Signing.wordAddress 0x80008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyH2Entry67.setupState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem setup_seed_words (s : MachineState) :
    ∀ i : Fin 2,
      (GroupedBalancedVerifyH2Entry67.setupState s).getMem
        (Signing.wordAddress 0x80020 i.val) =
      s.getMem (Signing.wordAddress 0x80020 i.val) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyH2Entry67.setupState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem setup_index_frame (s : MachineState) :
    ∀ i : Fin 3,
      (GroupedBalancedVerifyH2Entry67.setupState s).getMem
        (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyH2Entry67.setupState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

#print axioms setup_head
#print axioms setup_index_words
#print axioms setup_seed_words
#print axioms setup_index_frame
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Setup67
