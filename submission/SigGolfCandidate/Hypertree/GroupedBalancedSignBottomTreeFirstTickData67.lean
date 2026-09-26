import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstInput67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreNode67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePointerData67
/-! The first bottom-tree parent query starts with a witness copy and resets the parent counter. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private def selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private def copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private def paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private def children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (paired s)
private def ready (s : MachineState) :=
  GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)
def hashed (hash : Hash) (s : MachineState) :=
  writeHash (ready s) (hash (hashInput (ready s)))
def stored (hash : Hash) (s : MachineState) :=
  GroupedBalancedSignBottomTreeStoreData67.storedState (hashed hash s)
def advanced (hash : Hash) (s : MachineState) :=
  GroupedBalancedSignBottomTreeParentAdvance67.advanceState (stored hash s)
def tickState (hash : Hash) (s : MachineState) :=
  GroupedBalancedSignBottomTreeParentControl67.branchState (advanced hash s)
theorem hashed_from_paired (hash : Hash) (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (hashed hash s).getMem a = (paired s).getMem a := by
  have ne (b : Nat) (below : b < 0x81000) : a ≠ BitVec.ofNat 64 b := by
    intro h
    have hn := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at hn
    omega
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (paired s) a
    (ne 0x80020 (by decide)) (ne 0x80028 (by decide))
    (ne 0x80030 (by decide)) (ne 0x80038 (by decide))
  have readyFrame := GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame (children s) a
    (ne 0x80000 (by decide)) (ne 0x80008 (by decide))
    (ne 0x80010 (by decide)) (ne 0x80018 (by decide))
  have answerFrame : (hashed hash s).getMem a = (ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s))) args.2.2.1 a
    intro i same
    have hn := congrArg BitVec.toNat same
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
    omega
  exact answerFrame.trans (readyFrame.trans childFrame)
theorem hashed_high_frame (hash : Hash) (s : MachineState)
    (level : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (high : 0x81000 ≤ a.toNat) (counterNe : a ≠ 0x810d8) :
    (hashed hash s).getMem a = s.getMem a := by
  rw [hashed_from_paired hash s a high]
  change (GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)).getMem a = _
  rw [
    GroupedBalancedSignBottomTreePairStartData67.initial_frame (copied s) a counterNe]
  exact GroupedBalancedSignBottomTreeSelectData67.copied_high_frame
    s level a levelWord witnessBase levelBound (by omega)

private theorem ne_high_of_low (a : Word) (low : a.toNat < 0x20090)
    (b : Nat) (hb : 0x20090 ≤ b) (hbound : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at hn
  omega

theorem hashed_low_frame (hash : Hash) (s : MachineState)
    (level : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (low : a.toNat < 0x20090) :
    (hashed hash s).getMem a = s.getMem a := by
  have ne (b : Nat) (hb : 0x20090 ≤ b) (hbound : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := ne_high_of_low a low b hb hbound
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (paired s) a
    (ne 0x80020 (by decide) (by decide))
    (ne 0x80028 (by decide) (by decide))
    (ne 0x80030 (by decide) (by decide))
    (ne 0x80038 (by decide) (by decide))
  have readyFrame := GroupedBalancedSignBottomTreeH4Prelude67.prelude_frame
    (children s) a
    (ne 0x80000 (by decide) (by decide))
    (ne 0x80008 (by decide) (by decide))
    (ne 0x80010 (by decide) (by decide))
    (ne 0x80018 (by decide) (by decide))
  have answerFrame : (hashed hash s).getMem a = (ready s).getMem a := by
    have args := GroupedBalancedSignBottomTreeH4Prelude67.prelude_hash_args (children s)
    apply Signing.hash_answer_frame (ready s) (hash (hashInput (ready s)))
      args.2.2.1 a
    intro i same
    exact ne (0x80300+8*i.val) (by omega) (by omega) same
  have dest := GroupedBalancedSignBottomTreeSelectData67.selected_destination_nat
    s level levelWord witnessBase levelBound
  have dest' : ((selected s).getReg .x7).toNat = 0x20090+16*level := by
    simpa only [selected] using dest
  have dstLow : a ≠ (selected s).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [dest'] at hn
    omega
  have dstHigh : a ≠ (selected s).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,dest'] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega : 0x20090+16*level+8 < 2^64)] at hn
    omega
  exact answerFrame.trans (readyFrame.trans (childFrame.trans
    ((GroupedBalancedSignBottomTreePairStartData67.initial_frame (copied s) a
      (ne 0x810d8 (by decide) (by decide))).trans
      (GroupedBalancedSignBottomTreeSelectData67.copied_frame s a dstLow dstHigh))))
theorem hashed_counter (hash : Hash) (s : MachineState) :
    (hashed hash s).getMem 0x810d8 = 0 := by
  rw [hashed_from_paired hash s 0x810d8 (by decide)]
  change (GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)).getMem 0x810d8 = _
  exact GroupedBalancedSignBottomTreePairStartData67.initial_count (copied s)
theorem output_pointer (hash : Hash) (s : MachineState)
    (level target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 = BitVec.ofNat 64 target := by
  have targetWord : (hashed hash s).getMem 0x810c8 =
      BitVec.ofNat 64 target := by
    rw [hashed_high_frame hash s level 0x810c8 levelWord witnessBase
      levelBound (by decide) (by decide),destination]
  have ptr := GroupedBalancedSignBottomTreePointerData67.store_reg_nat
    (hashed hash s) 0 target (hashed_counter hash s) targetWord
  simpa only [Nat.mul_zero,Nat.add_zero] using ptr
theorem output_node (hash : Hash) (s : MachineState)
    (level tree sourceBase target : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 sourceBase)
    (sourceCase : sourceBase = 0x83000 ∨ sourceBase = 0x88000)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (sourceBase + 16 + 8*i.val)) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (stored hash s).getMem (BitVec.ofNat 64 (target + 8*i.val)) =
        (GroupedBottomTree.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
  have answer : ∀ i : Fin 2,
      (hashed hash s).getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
    exact GroupedBalancedSignBottomTreeFirstInput67.first_node_answer
      hash s level tree sourceBase left right levelWord witnessBase levelBound
      source sourceCase hlevel address leftWords rightWords
  have writes := GroupedBalancedSignBottomTreeStoreNode67.store_node
    (hashed hash s) (GroupedBottomTree.node hash level tree left right) answer
  intro i
  have p := output_pointer hash s level target levelWord witnessBase
    levelBound destination
  simpa only [stored,p,BitVec.ofNat_add] using writes i
theorem stored_from_hashed (hash : Hash) (s : MachineState)
    (level target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x83000) :
    (stored hash s).getMem a = (hashed hash s).getMem a := by
  have ptr := output_pointer hash s level target levelWord witnessBase
    levelBound destination
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr,BitVec.toNat_ofNat] at hn
    rcases targetCase with rfl | rfl <;> omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases targetCase with rfl | rfl
    · have v : ((BitVec.ofNat 64 0x83000) + 8).toNat = 0x83008 := by decide
      rw [v] at hn
      omega
    · have v : ((BitVec.ofNat 64 0x88000) + 8).toNat = 0x88008 := by decide
      rw [v] at hn
      omega
  exact GroupedBalancedSignBottomTreeStoreData67.stored_frame
    (hashed hash s) a h0 h1
theorem stored_control_frame (hash : Hash) (s : MachineState)
    (level target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000)
    (counterNe : a ≠ 0x810d8) :
    (stored hash s).getMem a = s.getMem a := by
  rw [stored_from_hashed hash s level target a levelWord witnessBase
    levelBound destination targetCase low]
  exact hashed_high_frame hash s level a levelWord witnessBase
    levelBound high counterNe
theorem tick_count (hash : Hash) (s : MachineState)
    (level target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem 0x810d8 = 1 := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_count,
    stored_from_hashed hash s level target 0x810d8 levelWord witnessBase
      levelBound destination targetCase (by decide),hashed_counter]
  decide
theorem tick_address (hash : Hash) (s : MachineState)
    (level target : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem 0x81008 = s.getMem 0x81008 + 1 := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_address,
    stored_control_frame hash s level target 0x81008 levelWord witnessBase
      levelBound destination targetCase (by decide) (by decide) (by decide)]
theorem tick_source_frame (hash : Hash) (s : MachineState)
    (level sourceBase target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (bases : (sourceBase = 0x83000 ∧ target = 0x88000) ∨
      (sourceBase = 0x88000 ∧ target = 0x83000))
    (sourceRange : sourceBase ≤ a.toNat ∧ a.toNat < sourceBase+0x4000) :
    (tickState hash s).getMem a = s.getMem a := by
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases bases with ⟨_,h⟩ | ⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have ptr := output_pointer hash s level target levelWord witnessBase
    levelBound destination
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr,BitVec.toNat_ofNat] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have v : ((BitVec.ofNat 64 0x88000) + 8).toNat = 0x88008 := by decide
      rw [v] at hn
      omega
    · have v : ((BitVec.ofNat 64 0x83000) + 8).toNat = 0x83008 := by decide
      rw [v] at hn
      omega
  have storeFrame : (stored hash s).getMem a = (hashed hash s).getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame
      (hashed hash s) a h0 h1
  have high : 0x81000 ≤ a.toNat := by
    rcases bases with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  have counterNe : a ≠ 0x810d8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp at hn
    omega
  have advFrame : (advanced hash s).getMem a = (stored hash s).getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storeFrame,
    hashed_high_frame hash s level a levelWord witnessBase levelBound high counterNe]
theorem tick_control_frame (hash : Hash) (s : MachineState)
    (level target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000)
    (counterNe : a ≠ 0x810d8) (addressNe : a ≠ 0x81008) :
    (tickState hash s).getMem a = s.getMem a := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_frame
      (stored hash s) a addressNe counterNe]
  exact stored_control_frame hash s level target a levelWord witnessBase
    levelBound destination targetCase high low counterNe

theorem tick_low_frame (hash : Hash) (s : MachineState)
    (level target : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x20090) :
    (tickState hash s).getMem a = s.getMem a := by
  have addressNe : a ≠ 0x81008 :=
    ne_high_of_low a low 0x81008 (by decide) (by decide)
  have counterNe : a ≠ 0x810d8 :=
    ne_high_of_low a low 0x810d8 (by decide) (by decide)
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_frame
      (stored hash s) a addressNe counterNe,
    stored_from_hashed hash s level target a levelWord witnessBase
      levelBound destination targetCase (by omega)]
  exact hashed_low_frame hash s level a levelWord witnessBase levelBound low
#print axioms hashed_from_paired
#print axioms hashed_high_frame
#print axioms hashed_counter
#print axioms output_pointer
#print axioms output_node
#print axioms stored_from_hashed
#print axioms stored_control_frame
#print axioms tick_count
#print axioms tick_address
#print axioms tick_source_frame
#print axioms tick_control_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickData67
