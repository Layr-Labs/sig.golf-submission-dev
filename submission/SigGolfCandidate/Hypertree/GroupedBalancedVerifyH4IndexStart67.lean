import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67

/-! The verifier's H2-to-H4 control transition leaves its three-word index
unchanged. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyH4IndexHeader67
open GroupedBalancedVerifyH4IndexFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem start_index_frame (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyTreeStart67.startState s) := by
  intro i
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeStart67.startState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne,
      Signing.wordAddress]

theorem start_root_frame (s : MachineState) (i : Fin 2) :
    (GroupedBalancedVerifyTreeStart67.startState s).getMem
        (Signing.wordAddress 0x80500 i.val) =
      s.getMem (Signing.wordAddress 0x80500 i.val) := by
  fin_cases i <;>
    simp [GroupedBalancedVerifyTreeStart67.startState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.getMem_setMem_ne,
      Signing.wordAddress]

theorem start_refines (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    StoredIndex (GroupedBalancedVerifyTreeStart67.startState s) index :=
  stored_of_frame (start_index_frame s) stored

theorem start_low (s : MachineState) :
    GroupedBalancedVerifyStackGlobal67.LowFrame s
      (GroupedBalancedVerifyTreeStart67.startState s) := by
  intro a low
  have ne48 : a ≠ (0x81048 : Word) :=
    GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81048
      (by decide) (by decide)
  have ne50 : a ≠ (0x81050 : Word) :=
    GroupedBalancedVerifyStackGlobal67.low_ne a low 0x81050
      (by decide) (by decide)
  simp [GroupedBalancedVerifyTreeStart67.startState,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  split_ifs with h1 h2
  · exact False.elim (ne50 h1)
  · exact False.elim (ne48 h2)
  · rfl

theorem start_index (s : MachineState) (index : BitVec 192)
    (pc : s.pc = 0x1264)
    (pointer : s.getMem 0x81048 = 0x2c720)
    (stored : StoredIndex s index) :
    OrdinarySteps image s 11 (GroupedBalancedVerifyTreeStart67.startState s) ∧
    (GroupedBalancedVerifyTreeStart67.startState s).pc = 0x1290 ∧
    (GroupedBalancedVerifyTreeStart67.startState s).getMem 0x81048 = 0x2c730 ∧
    (GroupedBalancedVerifyTreeStart67.startState s).getMem 0x81050 = 0 ∧
    StoredIndex (GroupedBalancedVerifyTreeStart67.startState s) index ∧
    GroupedBalancedVerifyStackGlobal67.LowFrame s
      (GroupedBalancedVerifyTreeStart67.startState s) := by
  have controls := GroupedBalancedVerifyTreeStart67.start_controls s pointer
  exact ⟨GroupedBalancedVerifyTreeStart67.start_steps s pc,
    GroupedBalancedVerifyTreeStart67.start_pc s pc,
    controls.1,controls.2,start_refines s index stored,start_low s⟩

#print axioms start_index
#print axioms start_root_frame
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexStart67
