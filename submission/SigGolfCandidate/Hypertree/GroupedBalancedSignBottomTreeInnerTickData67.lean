import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickFrame67
/-! Functional result and exact bytecode trace of one signing parent tick. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev pair := GroupedBalancedSignBottomTreePairPtrLoop67.pairState
private abbrev children := GroupedBalancedSignBottomTreeChildData67.childrenState
open GroupedBalancedSignBottomTreeInnerTickFrame67

theorem tick_trace (hash : Hash) (s : MachineState)
    (count source target : Nat) (pc : s.pc = 0x1f08)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (sourceBase : s.getMem 0x810c0 = BitVec.ofNat 64 source)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (sourceCase : source = 0x83000 ∨ source = 0x88000)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    Trace hash image s 84 91 1 1 (tickState hash s) := by
  let t1 := pair s
  let t2 := GroupedBalancedSignBottomTreePairLoad67.loadState t1
  let t3 := GroupedBalancedSignBottomTreeNodeInput67.inputState t2
  let t4 := hashed hash s
  let t5 := GroupedBalancedSignBottomTreeHashStorePtr67.storeState t4
  let t6 := GroupedBalancedSignBottomTreeHashStoreCopy67.copyState t5
  let t7 := GroupedBalancedSignBottomTreeParentAdvance67.advanceState t6
  let t8 := GroupedBalancedSignBottomTreeParentControl67.branchState t7
  have child (k : Nat) (bound : k ≤ 24) (aligned : k % 8 = 0) :
      accessValid (t1.getReg .x7 + BitVec.ofNat 64 k) 8 = true :=
    GroupedBalancedSignBottomTreePointerData67.pair_access s count source k
      counter sourceBase sourceCase countBound bound aligned
  have hashedCounter : t4.getMem 0x810d8 = BitVec.ofNat 64 count := by
    rw [hashed_high_frame hash s 0x810d8 (by decide),counter]
  have hashedTarget : t4.getMem 0x810c8 = BitVec.ofNat 64 target := by
    rw [hashed_high_frame hash s 0x810c8 (by decide),destination]
  have out (k : Nat) (bound : k ≤ 8) (aligned : k % 8 = 0) :
      accessValid (t5.getReg .x7 + BitVec.ofNat 64 k) 8 = true :=
    GroupedBalancedSignBottomTreePointerData67.store_access t4 count target k
      hashedCounter hashedTarget targetCase countBound bound aligned
  exact GroupedBalancedSignBottomTreeParentTick67.inner_tick hash
    s t1 t2 t3 t4 t5 t6 t7 t8 pc rfl rfl rfl rfl rfl rfl rfl rfl
    (by simpa using child 0 (by decide) (by decide))
    (by simpa using child 8 (by decide) (by decide))
    (by simpa using child 16 (by decide) (by decide))
    (by simpa using child 24 (by decide) (by decide))
    (by simpa using out 0 (by decide) (by decide))
    (by simpa using out 8 (by decide) (by decide))

theorem tick_pc (hash : Hash) (s : MachineState)
    (count target : Nat) (pc : s.pc = 0x1f08)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).pc =
      if s.getMem 0x810d8 + 1 ≠ s.getMem 0x810d0 then 0x1f08 else 0x2058 := by
  let t1 := pair s
  let t2 := GroupedBalancedSignBottomTreePairLoad67.loadState t1
  let t3 := GroupedBalancedSignBottomTreeNodeInput67.inputState t2
  let t4 := hashed hash s
  let t5 := GroupedBalancedSignBottomTreeHashStorePtr67.storeState t4
  let t6 := GroupedBalancedSignBottomTreeHashStoreCopy67.copyState t5
  let t7 := GroupedBalancedSignBottomTreeParentAdvance67.advanceState t6
  have p1 : t1.pc = 0x1f28 := GroupedBalancedSignBottomTreePairPtrLoop67.pair_pc s pc
  have p2 : t2.pc = 0x1f38 := GroupedBalancedSignBottomTreePairLoad67.load_pc t1 p1
  have p3 : t3.pc = 0x1f50 := GroupedBalancedSignBottomTreeNodeInput67.input_pc t2 p2
  have p4 : t4.pc = 0x1fd8 := by
    change (writeHash (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t3)
      (hash (hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t3)))).pc = _
    rw [Keygen.hash_pc,GroupedBalancedSignBottomTreeH4Prelude67.prelude_pc t3 p3]
    decide
  have p5 : t5.pc = 0x2008 := GroupedBalancedSignBottomTreeHashStorePtr67.store_pc t4 p4
  have p6 : t6.pc = 0x2010 := GroupedBalancedSignBottomTreeHashStoreCopy67.copy_pc t5 p5
  have p7 : t7.pc = 0x2054 := GroupedBalancedSignBottomTreeParentAdvance67.advance_pc t6 p6
  have regs := GroupedBalancedSignBottomTreeParentControl67.advance_regs t6
  have c : t6.getMem 0x810d8 = s.getMem 0x810d8 :=
    stored_below_frame hash s count target 0x810d8 counter destination
      countBound targetCase (by decide) (by decide)
  have limit : t6.getMem 0x810d0 = s.getMem 0x810d0 :=
    stored_below_frame hash s count target 0x810d0 counter destination
      countBound targetCase (by decide) (by decide)
  change (GroupedBalancedSignBottomTreeParentControl67.branchState t7).pc = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_pc t7 p7,
    regs.1,regs.2,c,limit]

theorem input_query (s : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
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
    hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState
      (children (pair s))) =
      Reference.packed (KeygenNode.payload level tree left right) := by
  apply GroupedBalancedSignBottomTreeH4Query67.node_query
  · rw [GroupedBalancedSignBottomTreeChildData67.frame (pair s) 0x81000
      (by decide) (by decide) (by decide) (by decide),
      GroupedBalancedSignBottomTreePointerData67.pair_frame,levelWord]
  · intro i
    rw [GroupedBalancedSignBottomTreeChildData67.frame (pair s) _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide),
      GroupedBalancedSignBottomTreePointerData67.pair_frame]
    exact address i
  · intro i
    rw [GroupedBalancedSignBottomTreeChildData67.left_words (pair s) i,
      GroupedBalancedSignBottomTreePointerData67.pair_frame]
    exact leftWords i
  · intro i
    rw [GroupedBalancedSignBottomTreeChildData67.right_words (pair s) i,
      GroupedBalancedSignBottomTreePointerData67.pair_frame]
    exact rightWords i

theorem output_frame (hash : Hash) (s : MachineState)
    (count target : Nat) (i : Fin 2)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (tickState hash s).getMem
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7 +
        BitVec.ofNat 64 (8*i.val)) =
    (stored hash s).getMem
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7 +
        BitVec.ofNat 64 (8*i.val)) := by
  let a := (GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7 +
    BitVec.ofNat 64 (8*i.val)
  have ptr := output_pointer_nat hash s count target counter destination countBound targetCase
  have targetRange : 0x83000 ≤ target ∧ target ≤ 0x88000 := by
    rcases targetCase with rfl | rfl <;> omega
  have addrNat : a.toNat = target+16*count+8*i.val := by
    dsimp only [a]
    rw [BitVec.toNat_add,ptr,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8*i.val < 2^64),
      Nat.mod_eq_of_lt (by omega : target+16*count+8*i.val < 2^64)]
  have h0 : a ≠ 0x81008#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [addrNat] at hn; simp at hn; omega
  have h1 : a ≠ 0x810d8#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [addrNat] at hn; simp at hn; omega
  change (tickState hash s).getMem a = (stored hash s).getMem a
  rw [tickState,GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    advanced,GroupedBalancedSignBottomTreeParentControl67.advance_frame _ a h0 h1]

theorem output_node (hash : Hash) (s : MachineState)
    (count target level tree : Nat) (left right : Reference.Digest)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
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
      (tickState hash s).getMem
        ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState (hashed hash s)).getReg .x7 +
          BitVec.ofNat 64 (8*i.val)) =
        (GroupedBottomTree.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
  have answer := GroupedBalancedSignBottomTreeInnerQueryData67.inner_node_answer
    hash s level tree left right levelWord address leftWords rightWords
  have storedAnswer := GroupedBalancedSignBottomTreeStoreNode67.store_node
    (hashed hash s) (GroupedBottomTree.node hash level tree left right) answer
  intro i
  exact (output_frame hash s count target i counter destination countBound targetCase).trans
    (storedAnswer i)

theorem output_node_at (hash : Hash) (s : MachineState)
    (count target level tree : Nat) (left right : Reference.Digest)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
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
      (tickState hash s).getMem
        (BitVec.ofNat 64 (target+16*count+8*i.val)) =
      (GroupedBottomTree.node hash level tree left right).extractLsb'
        (64*i.val) 64 := by
  intro i
  have h := output_node hash s count target level tree left right
    counter destination countBound targetCase levelWord address leftWords rightWords i
  rw [output_pointer hash s count target counter destination] at h
  simpa only [BitVec.ofNat_add,show 16*count+8*i.val = 16*count+8*i.val by rfl]
    using h

#print axioms tick_trace
#print axioms input_query
#print axioms output_frame
#print axioms output_node
#print axioms output_node_at
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickData67
