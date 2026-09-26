import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairLoad67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeNodeInput67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeChildData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
def childrenState (s : MachineState) : MachineState :=
  GroupedBalancedSignBottomTreeNodeInput67.inputState
    (GroupedBalancedSignBottomTreePairLoad67.loadState s)
theorem left_words (s : MachineState) :
    ∀ i : Fin 2,
      (childrenState s).getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (s.getReg .x7 + BitVec.ofNat 64 (8*i.val)) := by
  intro i
  fin_cases i <;>
    simp [childrenState,GroupedBalancedSignBottomTreeNodeInput67.inputState,
      GroupedBalancedSignBottomTreePairLoad67.loadState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem right_words (s : MachineState) :
    ∀ i : Fin 2,
      (childrenState s).getMem (Signing.wordAddress 0x80030 i.val) =
        s.getMem (s.getReg .x7 + BitVec.ofNat 64 (16+8*i.val)) := by
  intro i
  fin_cases i <;>
    simp [childrenState,GroupedBalancedSignBottomTreeNodeInput67.inputState,
      GroupedBalancedSignBottomTreePairLoad67.loadState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80020) (h1 : a ≠ 0x80028)
    (h2 : a ≠ 0x80030) (h3 : a ≠ 0x80038) :
    (childrenState s).getMem a = s.getMem a := by
  change a ≠ 524320#64 at h0
  change a ≠ 524328#64 at h1
  change a ≠ 524336#64 at h2
  change a ≠ 524344#64 at h3
  simp [childrenState,GroupedBalancedSignBottomTreeNodeInput67.inputState,
    GroupedBalancedSignBottomTreePairLoad67.loadState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3]
#print axioms left_words
#print axioms right_words
#print axioms frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeChildData67
