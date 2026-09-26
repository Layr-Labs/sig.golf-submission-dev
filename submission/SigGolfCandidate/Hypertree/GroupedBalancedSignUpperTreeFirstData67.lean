import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreNode67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstInput67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstData67. -/
section
/-! H4 input and first parent digest for the upper-tree callee. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstInput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private abbrev copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private abbrev paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private abbrev input (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (paired s)

theorem paired_source_word (s : MachineState)
    (level witnessBase base : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) (i : Fin 4) :
    (paired s).getMem ((paired s).getReg .x7 + BitVec.ofNat 64 (8*i.val)) =
      s.getMem (BitVec.ofNat 64 (base + 8*i.val)) := by
  have ptr := GroupedBalancedSignUpperTreeFirstTick67.paired_pointer s level
    witnessBase levelWord witness levelBound witnessBound
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
  exact GroupedBalancedSignUpperTreeSelect67.copied_high_frame s level
    witnessBase _ levelWord witness levelBound witnessBound high

theorem input_level (s : MachineState) (level witnessBase : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000) :
    (input s).getMem 0x81000 = s.getMem 0x81000 := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (paired s) 0x81000 (by decide) (by decide) (by decide) (by decide),
    GroupedBalancedSignBottomTreePairStartData67.initial_frame
      (copied s) 0x81000 (by decide)]
  exact GroupedBalancedSignUpperTreeSelect67.copied_high_frame s level
    witnessBase _ levelWord witness levelBound witnessBound (by decide)

theorem input_address (s : MachineState) (level witnessBase : Nat)
    (i : Fin 3)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000) :
    (input s).getMem (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (paired s) _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide),
    GroupedBalancedSignBottomTreePairStartData67.initial_frame
      (copied s) _ (by fin_cases i <;> decide)]
  exact GroupedBalancedSignUpperTreeSelect67.copied_high_frame s level
    witnessBase _ levelWord witness levelBound witnessBound
      (by fin_cases i <;> decide)

theorem input_left (s : MachineState) (level witnessBase base : Nat)
    (i : Fin 2)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) :
    (input s).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem (BitVec.ofNat 64 (base + 8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.left_words]
  exact paired_source_word s level witnessBase base levelWord witness levelBound
    witnessBound source baseCase ⟨i.val,by omega⟩

theorem input_right (s : MachineState) (level witnessBase base : Nat)
    (i : Fin 2)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000) :
    (input s).getMem (Signing.wordAddress 0x80030 i.val) =
      s.getMem (BitVec.ofNat 64 (base + 16+8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.right_words]
  simpa only [show 8 * (2+i.val) = 16 + 8*i.val by omega,
    Nat.add_assoc]
    using paired_source_word s level witnessBase base levelWord witness levelBound
      witnessBound source baseCase ⟨2+i.val,by omega⟩

theorem first_node_answer (hash : Hash) (s : MachineState)
    (level witnessBase treeLevel treeAddress sourceBase : Nat)
    (left right : Reference.Digest)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 sourceBase)
    (baseCase : sourceBase = 0x83000 ∨ sourceBase = 0x88000)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 treeLevel)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 treeAddress).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 16 + 8*i.val)) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash
        (GroupedBalancedSignBottomTreeH4Prelude67.preludeState (input s))
        (hash (hashInput
          (GroupedBalancedSignBottomTreeH4Prelude67.preludeState (input s))))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.node hash treeLevel treeAddress left right).extractLsb'
          (64*i.val) 64 := by
  exact GroupedBalancedSignBottomTreeH4Query67.node_answer hash
    (input s) treeLevel treeAddress left right
    (by rw [input_level s level witnessBase levelWord witness levelBound
      witnessBound]; exact hlevel)
    (by intro i; rw [input_address s level witnessBase i levelWord witness
      levelBound witnessBound]; exact address i)
    (by intro i; rw [input_left s level witnessBase sourceBase i levelWord
      witness levelBound witnessBound source baseCase]; exact leftWords i)
    (by intro i; rw [input_right s level witnessBase sourceBase i levelWord
      witness levelBound witnessBound source baseCase]; exact rightWords i)

#print axioms first_node_answer
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstInput67

end

/-! Semantic H4 output of the upper tree's first parent tick. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev hashed := GroupedBalancedSignBottomTreeFirstTickData67.hashed
private abbrev stored := GroupedBalancedSignBottomTreeFirstTickData67.stored
private abbrev tick := GroupedBalancedSignBottomTreeFirstTickData67.tickState

theorem output_node (hash : Hash) (s : MachineState)
    (level witnessBase treeLevel treeAddress sourceBase target : Nat)
    (left right : Reference.Digest)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 sourceBase)
    (sourceCase : sourceBase = 0x83000 ∨ sourceBase = 0x88000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 treeLevel)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 treeAddress).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 16 + 8*i.val)) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (stored hash s).getMem (BitVec.ofNat 64 (target + 8*i.val)) =
        (GroupedBottomTree.node hash treeLevel treeAddress left right).extractLsb'
          (64*i.val) 64 := by
  have answer : ∀ i : Fin 2,
      (hashed hash s).getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.node hash treeLevel treeAddress left right).extractLsb'
          (64*i.val) 64 := by
    exact GroupedBalancedSignUpperTreeFirstInput67.first_node_answer
      hash s level witnessBase treeLevel treeAddress sourceBase left right
      levelWord witness levelBound witnessBound source sourceCase hlevel address
      leftWords rightWords
  have writes := GroupedBalancedSignBottomTreeStoreNode67.store_node
    (hashed hash s) (GroupedBottomTree.node hash treeLevel treeAddress
      left right) answer
  intro i
  have p := GroupedBalancedSignUpperTreeFirstTick67.output_pointer hash s
    level witnessBase target levelWord witness levelBound witnessBound
    destination
  simpa only [stored,GroupedBalancedSignBottomTreeFirstTickData67.stored,
    p,BitVec.ofNat_add] using writes i

theorem tick_output (hash : Hash) (s : MachineState)
    (level witnessBase treeLevel treeAddress sourceBase target : Nat)
    (left right : Reference.Digest)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 sourceBase)
    (sourceCase : sourceBase = 0x83000 ∨ sourceBase = 0x88000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 treeLevel)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 treeAddress).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 16 + 8*i.val)) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (tick hash s).getMem (BitVec.ofNat 64 (target + 8*i.val)) =
        (GroupedBottomTree.node hash treeLevel treeAddress left right).extractLsb'
          (64*i.val) 64 := by
  intro i
  have prior := output_node hash s level witnessBase treeLevel treeAddress
    sourceBase target left right levelWord witness levelBound witnessBound
    source sourceCase destination hlevel address leftWords rightWords i
  have addrNe (b : Nat) (hb : b < 0x83000) :
      BitVec.ofNat 64 (target+8*i.val) ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    have targetRange : 0x83000 ≤ target ∧ target ≤ 0x88000 := by
      rcases targetCase with rfl | rfl <;> omega
    simp only [BitVec.toNat_ofNat] at hn
    rw [Nat.mod_eq_of_lt (by omega : target+8*i.val < 2^64),
      Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem _ = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_frame _ _
      (addrNe 0x81008 (by decide)) (addrNe 0x810d8 (by decide))]
  exact prior

#print axioms output_node
#print axioms tick_output
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstData67
