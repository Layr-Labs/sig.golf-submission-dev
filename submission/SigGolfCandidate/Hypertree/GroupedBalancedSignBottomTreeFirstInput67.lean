import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairPtr67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeChildData67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairStartData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev pair := GroupedBalancedSignBottomTreePairPtr67.pairState
theorem initial_pointer (s : MachineState) :
    (pair s).getReg .x7 = s.getMem 0x810c0 := by
  simp [GroupedBalancedSignBottomTreePairPtr67.pairState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem initial_count (s : MachineState) :
    (pair s).getMem 0x810d8 = 0 := by
  simp [GroupedBalancedSignBottomTreePairPtr67.pairState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem initial_frame (s : MachineState) (a : Word)
    (outside : a ≠ 0x810d8) :
    (pair s).getMem a = s.getMem a := by
  change a ≠ 528600#64 at outside
  simp [GroupedBalancedSignBottomTreePairPtr67.pairState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]
#print axioms initial_pointer
#print axioms initial_count
#print axioms initial_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairStartData67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstInput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private abbrev copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private abbrev paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private abbrev input (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (paired s)
theorem paired_pointer (s : MachineState) (level : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10) :
    (paired s).getReg .x7 = s.getMem 0x810c0 := by
  rw [paired,GroupedBalancedSignBottomTreePairStartData67.initial_pointer]
  exact GroupedBalancedSignBottomTreeSelectData67.copied_high_frame
    s level 0x810c0 levelWord witnessBase levelBound (by decide)
theorem paired_source_word (s : MachineState) (level base : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) (i : Fin 4) :
    (paired s).getMem ((paired s).getReg .x7 + BitVec.ofNat 64 (8*i.val)) =
      s.getMem (BitVec.ofNat 64 (base + 8*i.val)) := by
  have ptr := paired_pointer s level levelWord witnessBase levelBound
  have addr : s.getMem 0x810c0 + BitVec.ofNat 64 (8*i.val) =
      BitVec.ofNat 64 (base + 8*i.val) := by
    rw [source]
    simp [BitVec.ofNat_add]
  have notCounter : BitVec.ofNat 64 (base + 8*i.val) ≠ 0x810d8 := by
    fin_cases i <;> rcases baseCase with rfl | rfl <;> decide
  have high : 0x80000 ≤ (BitVec.ofNat 64 (base + 8*i.val)).toNat := by
    fin_cases i <;> rcases baseCase with rfl | rfl <;> decide
  rw [ptr,addr,GroupedBalancedSignBottomTreePairStartData67.initial_frame
    (copied s) _ notCounter]
  exact GroupedBalancedSignBottomTreeSelectData67.copied_high_frame
    s level _ levelWord witnessBase levelBound high
theorem input_level (s : MachineState) (level : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10) :
    (input s).getMem 0x81000 = s.getMem 0x81000 := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (paired s) 0x81000 (by decide) (by decide) (by decide) (by decide),
    GroupedBalancedSignBottomTreePairStartData67.initial_frame
      (copied s) 0x81000 (by decide)]
  exact GroupedBalancedSignBottomTreeSelectData67.copied_high_frame
    s level _ levelWord witnessBase levelBound (by decide)
theorem input_address (s : MachineState) (level : Nat) (i : Fin 3)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10) :
    (input s).getMem (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (paired s) _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    GroupedBalancedSignBottomTreePairStartData67.initial_frame
      (copied s) _ (by fin_cases i <;> decide)]
  exact GroupedBalancedSignBottomTreeSelectData67.copied_high_frame
    s level _ levelWord witnessBase levelBound (by fin_cases i <;> decide)
theorem input_left (s : MachineState) (level base : Nat) (i : Fin 2)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) :
    (input s).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem (BitVec.ofNat 64 (base + 8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.left_words]
  exact paired_source_word s level base levelWord witnessBase levelBound
    source baseCase ⟨i.val,by omega⟩
theorem input_right (s : MachineState) (level base : Nat) (i : Fin 2)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) :
    (input s).getMem (Signing.wordAddress 0x80030 i.val) =
      s.getMem (BitVec.ofNat 64 (base + 16+8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.right_words]
  simpa only [show 8 * (2+i.val) = 16 + 8*i.val by omega,
    Nat.add_assoc]
    using paired_source_word s level base levelWord witnessBase levelBound
      source baseCase ⟨2+i.val,by omega⟩
theorem first_node_answer (hash : Hash) (s : MachineState)
    (level tree base : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (base + 8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (base + 16 + 8*i.val)) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash
        (GroupedBalancedSignBottomTreeH4Prelude67.preludeState (input s))
        (hash (hashInput
          (GroupedBalancedSignBottomTreeH4Prelude67.preludeState (input s))))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
  exact GroupedBalancedSignBottomTreeH4Query67.node_answer hash
    (input s) level tree left right
    (by rw [input_level s level levelWord witnessBase levelBound]; exact hlevel)
    (by intro i; rw [input_address s level i levelWord witnessBase levelBound]; exact address i)
    (by intro i; rw [input_left s level base i levelWord witnessBase levelBound
      source baseCase]; exact leftWords i)
    (by intro i; rw [input_right s level base i levelWord witnessBase levelBound
      source baseCase]; exact rightWords i)
#print axioms paired_pointer
#print axioms paired_source_word
#print axioms input_level
#print axioms input_address
#print axioms input_left
#print axioms input_right
#print axioms first_node_answer
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstInput67
