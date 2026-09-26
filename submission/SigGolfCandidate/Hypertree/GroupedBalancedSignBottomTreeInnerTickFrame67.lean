import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePointerData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeChildData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreNode67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerQueryData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private def pair (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtrLoop67.pairState s
private def input (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (pair s)
theorem input_level (s : MachineState) :
    (input s).getMem 0x81000 = s.getMem 0x81000 := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (pair s) 0x81000 (by decide) (by decide) (by decide) (by decide)]
  exact GroupedBalancedSignBottomTreePointerData67.pair_frame s _
theorem input_address (s : MachineState) (i : Fin 3) :
    (input s).getMem (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.frame
    (pair s) _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
  exact GroupedBalancedSignBottomTreePointerData67.pair_frame s _
theorem input_left (s : MachineState) (i : Fin 2) :
    (input s).getMem (Signing.wordAddress 0x80020 i.val) =
      s.getMem ((pair s).getReg .x7 + BitVec.ofNat 64 (8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.left_words (pair s) i]
  exact GroupedBalancedSignBottomTreePointerData67.pair_frame s _
theorem input_right (s : MachineState) (i : Fin 2) :
    (input s).getMem (Signing.wordAddress 0x80030 i.val) =
      s.getMem ((pair s).getReg .x7 + BitVec.ofNat 64 (16+8*i.val)) := by
  rw [input,GroupedBalancedSignBottomTreeChildData67.right_words (pair s) i]
  exact GroupedBalancedSignBottomTreePointerData67.pair_frame s _
theorem inner_node_answer (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem ((pair s).getReg .x7 + BitVec.ofNat 64 (8*i.val)) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem ((pair s).getReg .x7 + BitVec.ofNat 64 (16+8*i.val)) =
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
    (by rw [input_level,levelWord])
    (by intro i; rw [input_address]; exact address i)
    (by intro i; rw [input_left]; exact leftWords i)
    (by intro i; rw [input_right]; exact rightWords i)
#print axioms inner_node_answer
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerQueryData67

/-! Memory frames for one signing parent-tree tick. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private def pair (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtrLoop67.pairState s
private def children (s : MachineState) :=
  GroupedBalancedSignBottomTreeChildData67.childrenState (pair s)
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

theorem hashed_high_frame (hash : Hash) (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (hashed hash s).getMem a = s.getMem a := by
  have ne (b : Nat) (below : b < 0x81000) : a ≠ BitVec.ofNat 64 b := by
    intro h
    have hn := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at hn
    omega
  have pairFrame := GroupedBalancedSignBottomTreePointerData67.pair_frame s a
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (pair s) a
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
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

private theorem ne_high_of_low (a : Word) (low : a.toNat < 0x20090)
    (b : Nat) (hb : 0x20090 ≤ b) (hbound : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at hn
  omega

theorem hashed_low_frame (hash : Hash) (s : MachineState) (a : Word)
    (low : a.toNat < 0x20090) :
    (hashed hash s).getMem a = s.getMem a := by
  have ne (b : Nat) (hb : 0x20090 ≤ b) (hbound : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := ne_high_of_low a low b hb hbound
  have pairFrame := GroupedBalancedSignBottomTreePointerData67.pair_frame s a
  have childFrame := GroupedBalancedSignBottomTreeChildData67.frame (pair s) a
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
  exact answerFrame.trans (readyFrame.trans (childFrame.trans pairFrame))

theorem output_pointer (hash : Hash) (s : MachineState) (count target : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7 =
      BitVec.ofNat 64 (target+16*count) := by
  apply GroupedBalancedSignBottomTreePointerData67.store_reg_nat
  · rw [hashed_high_frame hash s 0x810d8 (by decide),counter]
  · rw [hashed_high_frame hash s 0x810c8 (by decide),destination]

theorem output_pointer_nat (hash : Hash) (s : MachineState) (count target : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7).toNat =
      target+16*count := by
  rw [output_pointer hash s count target counter destination,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  rcases targetCase with rfl | rfl <;> omega

theorem stored_below_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000) :
    (stored hash s).getMem a = s.getMem a := by
  have ptr := output_pointer_nat hash s count target counter destination
    countBound targetCase
  have targetLow : 0x83000 ≤ target := by rcases targetCase with rfl | rfl <;> omega
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptr] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega : target+16*count+8 < 2^64)] at hn
    omega
  rw [stored,GroupedBalancedSignBottomTreeStoreData67.stored_frame _ a h0 h1]
  exact hashed_high_frame hash s a high

theorem stored_low_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (low : a.toNat < 0x20090) :
    (stored hash s).getMem a = s.getMem a := by
  have ptr := output_pointer_nat hash s count target counter destination
    countBound targetCase
  have targetLow : 0x83000 ≤ target := by
    rcases targetCase with rfl | rfl <;> omega
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptr] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega : target+16*count+8 < 2^64)] at hn
    omega
  rw [stored,GroupedBalancedSignBottomTreeStoreData67.stored_frame _ a h0 h1]
  exact hashed_low_frame hash s a low

theorem tick_count (hash : Hash) (s : MachineState) (count target : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem 0x810d8 = s.getMem 0x810d8 + 1 := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_count,
    stored_below_frame hash s count target 0x810d8 counter destination
      countBound targetCase (by decide) (by decide)]

theorem tick_address (hash : Hash) (s : MachineState) (count target : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem 0x81008 = s.getMem 0x81008 + 1 := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_address,
    stored_below_frame hash s count target 0x81008 counter destination
      countBound targetCase (by decide) (by decide)]

theorem tick_control_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (high : 0x81000 ≤ a.toNat) (low : a.toNat < 0x83000)
    (neAddress : a ≠ 0x81008) (neCounter : a ≠ 0x810d8) :
    (tickState hash s).getMem a = s.getMem a := by
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_frame
      (stored hash s) a neAddress neCounter,
    stored_below_frame hash s count target a counter destination
      countBound targetCase high low]

theorem tick_low_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
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
    stored_low_frame hash s count target a counter destination
      countBound targetCase low]

theorem tick_source_frame (hash : Hash) (s : MachineState)
    (count source target : Nat) (a : Word)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000))
    (sourceRange : source ≤ a.toNat ∧ a.toNat < source+0x4000) :
    (tickState hash s).getMem a = s.getMem a := by
  have ptr := output_pointer_nat hash s count target counter destination
    countBound (by
      rcases bases with ⟨_,h⟩ | ⟨_,h⟩
      · exact Or.inr h
      · exact Or.inl h)
  have different0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [ptr] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  have different1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [BitVec.toNat_add,ptr] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega)] at hn
    rcases bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  have storeFrame : (stored hash s).getMem a = (hashed hash s).getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame
      (hashed hash s) a different0 different1
  have high : 0x81000 ≤ a.toNat := by
    rcases bases with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  have advFrame : (advanced hash s).getMem a = (stored hash s).getMem a := by
    apply GroupedBalancedSignBottomTreeParentControl67.advance_frame
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
    · intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storeFrame,hashed_high_frame hash s a high]

theorem tick_source_slots (hash : Hash) (s : MachineState)
    (count source target j : Nat) (i : Fin 2)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512) (slotBound : j < 1024)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000)) :
    (tickState hash s).getMem
      (BitVec.ofNat 64 (source+16*j+8*i.val)) =
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) := by
  apply tick_source_frame hash s count source target _ counter destination
    countBound bases
  have sourceBound : 0x83000 ≤ source ∧ source ≤ 0x88000 := by
    rcases bases with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
    (by omega : source+16*j+8*i.val < 2^64)]
  omega

theorem tick_prior_output_slots (hash : Hash) (s : MachineState)
    (count target j : Nat) (i : Fin 2)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512) (prior : j < count)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem
      (BitVec.ofNat 64 (target+16*j+8*i.val)) =
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) := by
  let a := BitVec.ofNat 64 (target+16*j+8*i.val)
  have ptr := output_pointer_nat hash s count target counter destination
    countBound targetCase
  have targetRange : 0x83000 ≤ target ∧ target ≤ 0x88000 := by
    rcases targetCase with rfl | rfl <;> omega
  have iBound := i.isLt
  have targetMax := targetRange.2
  have jBound : j < 512 := by omega
  have addrSmall : target+16*j+8*i.val < 2^64 := by
    have upper : target+16*j+8*i.val ≤ 0x88000+16*511+8 := by omega
    exact lt_of_le_of_lt upper (by decide)
  have addrSmall64 : target+16*j+8*i.val < 18446744073709551616 := by
    simpa only [show 2^64 = 18446744073709551616 by decide] using addrSmall
  have addrNat : a.toNat = target+16*j+8*i.val := by
    simpa only [a,BitVec.toNat_ofNat] using Nat.mod_eq_of_lt addrSmall64
  have h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [addrNat,ptr] at hn
    omega
  have h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState
      (hashed hash s)).getReg .x7 + 8 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [addrNat,BitVec.toNat_add,ptr] at hn
    have eight : (8 : Word).toNat = 8 := by decide
    rw [eight,Nat.mod_eq_of_lt (by omega : target+16*count+8 < 2^64)] at hn
    omega
  have storedFrame : (stored hash s).getMem a = (hashed hash s).getMem a :=
    GroupedBalancedSignBottomTreeStoreData67.stored_frame
      (hashed hash s) a h0 h1
  have high : 0x81000 ≤ a.toNat := by omega
  have hne08 : a ≠ 0x81008 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [addrNat] at hn; simp at hn; omega
  have hneD8 : a ≠ 0x810d8 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [addrNat] at hn; simp at hn; omega
  have advFrame : (advanced hash s).getMem a = (stored hash s).getMem a :=
    GroupedBalancedSignBottomTreeParentControl67.advance_frame
      (stored hash s) a hne08 hneD8
  change (tickState hash s).getMem a = s.getMem a
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advFrame,storedFrame,hashed_high_frame hash s a high]

#print axioms hashed_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67
