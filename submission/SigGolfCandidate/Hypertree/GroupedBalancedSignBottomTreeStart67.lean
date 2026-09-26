import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInitData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67

/-! The completed leaf table enters the first parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
private abbrev call := GroupedBalancedSignBottomTreeCall67.callState
private abbrev entry := GroupedBalancedSignBottomTreeEntry67.entryState
private abbrev init := GroupedBalancedSignBottomTreeInit67.initState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode

theorem selected_mask_bound (s : MachineState)
    (selected : s.getMem 0x810e8 =
      (s.getMem 0x81090 &&& 1023#64)) :
    (s.getMem 0x810e8).toNat < 1024 := by
  rw [selected,BitVec.toNat_and]
  have h : (s.getMem 0x81090).toNat &&& 1023 ≤ 1023 :=
    Nat.and_le_right
  norm_num at *
  omega

theorem first_params (base : Nat)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160) :
    Params base 0 512 0x83000 0x88000 (base/2) := by
  have hdiv : (base/2) % 512 = 0 := by omega
  have hbound : base/2 + 512 < 2^160 := by omega
  exact ⟨by decide,by decide,by decide,by simpa using aligned,
    by norm_num,hdiv,hbound,Or.inl ⟨rfl,rfl⟩⟩

theorem first_start (hash : Hash) (secretKey : SecretKey)
    (base : Nat) (s : MachineState)
    (pc : s.pc = 0x14ec)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160)
    (count : s.getMem 0x810d0 = 1024)
    (height : s.getMem 0x81000 = 0)
    (maxLevel : s.getMem 0x81060 = 10)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 base).extractLsb' (64*i.val) 64)
    (leafWords : ∀ j, j < 1024 → ∀ i : Fin 2,
      s.getMem (GroupedBalancedSignBottomStackSlots67.slot j i.val) =
        (GroupedBottomTree.leafRoot hash secretKey (base+j)).extractLsb'
          (64*i.val) 64) :
    ∃ t : MachineState,
      Trace hash image s 72 72 0 0 t ∧
      Params base 0 512 0x83000 0x88000 (base/2) ∧
      GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
        base 0 512 0x83000 0x88000 (base/2) t := by
  let called := call s
  let entered := entry called
  let prepared := init entered
  have callTrace := GroupedBalancedSignBottomTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignBottomTreeCall67.call_pc s pc
  have callSp : called.getReg .x2 = 0xfff7e0 ∨
      called.getReg .x2 = 0xfff700 := by
    rw [GroupedBalancedSignBottomTreeCall67.call_stack]
    exact sp
  have stackBelow (a : Word) (ha : a.toNat < 0x90000) :
      a ≠ called.getReg .x2 - 16 := by
    rcases callSp with h | h
    · rw [h]
      intro eq
      have hn : a.toNat = 0xfff7d0 := by rw [eq]; decide
      omega
    · rw [h]
      intro eq
      have hn : a.toNat = 0xfff6f0 := by rw [eq]; decide
      omega
  have entryTrace := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc callSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initTrace := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  have before (a : Word) (hstack : a.toNat < 0x90000)
      (hlevel : a ≠ 0x81050) (hsource : a ≠ 0x810c0)
      (htarget : a ≠ 0x810c8) (hcount : a ≠ 0x810d0) :
      prepared.getMem a = s.getMem a := by
    rw [GroupedBalancedSignBottomTreeInitData67.init_frame entered a
        hsource htarget hcount,
      GroupedBalancedSignBottomTreeEntryData67.entry_frame called a
        (stackBelow a hstack) hlevel,
      GroupedBalancedSignBottomTreeCall67.call_mem s a]
  have preparedScratch : ∀ i : Fin 3,
      prepared.getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 base).extractLsb' (64*i.val) 64 := by
    intro i
    rw [before _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact scratch i
  obtain ⟨t,prelude,pcOut,addressWords,scratchWords,frame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      prepared (BitVec.ofNat 192 base) initPc preparedScratch
  have shift : (BitVec.ofNat 192 base >>> 1) =
      BitVec.ofNat 192 (base/2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have preserve (a : Word)
      (h0 : a ≠ 0x81008) (h1 : a ≠ 0x81010)
      (h2 : a ≠ 0x81018) (h3 : a ≠ 0x810a8)
      (h4 : a ≠ 0x810b0) (h5 : a ≠ 0x810b8) :
      t.getMem a = prepared.getMem a :=
    frame a h0 h1 h2 h3 h4 h5
  have run : Trace hash image s 72 72 0 0 t := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((OrdinarySteps.trace (hash := hash) callTrace).trans
        (OrdinarySteps.trace (hash := hash) entryTrace)).trans
        (OrdinarySteps.trace (hash := hash) initTrace)).trans
        (OrdinarySteps.trace (hash := hash) prelude)
  refine ⟨t,run,first_params base aligned bounded,?_⟩
  refine ⟨pcOut,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [preserve 0x81050 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      GroupedBalancedSignBottomTreeInitData67.init_frame entered 0x81050
        (by decide) (by decide) (by decide)]
    exact GroupedBalancedSignBottomTreeEntry67.entry_level called
  · rw [preserve 0x810f8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      before 0x810f8 (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact witnessBase
  · rw [preserve 0x810e8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      before 0x810e8 (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact selectedBound
  · rw [preserve 0x810c0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact GroupedBalancedSignBottomTreeInitData67.init_source entered
  · rw [preserve 0x810c8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact GroupedBalancedSignBottomTreeInitData67.init_target entered
  · rw [preserve 0x810d0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      GroupedBalancedSignBottomTreeInitData67.init_count,
      GroupedBalancedSignBottomTreeEntryData67.entry_frame called
        0x810d0 (stackBelow 0x810d0 (by decide)) (by decide),
      GroupedBalancedSignBottomTreeCall67.call_mem,count]
    decide
  · rw [preserve 0x81000 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      before 0x81000 (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact height
  · intro i
    rw [addressWords i,shift]
  · intro j hj i
    let a := BitVec.ofNat 64 (0x83000+16*j+8*i.val)
    have addrNat : a.toNat = 0x83000+16*j+8*i.val := by
      simp only [a,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    have below : a.toNat < 0x87000 := by rw [addrNat]; omega
    have above : 0x83000 ≤ a.toNat := by rw [addrNat]; omega
    have neBelow (b : Word) (hb : b.toNat < 0x83000) : a ≠ b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      omega
    rw [preserve a (neBelow _ (by decide)) (neBelow _ (by decide))
      (neBelow _ (by decide)) (neBelow _ (by decide))
      (neBelow _ (by decide)) (neBelow _ (by decide)),
      before a (by omega) (neBelow _ (by decide))
        (neBelow _ (by decide)) (neBelow _ (by decide))
        (neBelow _ (by decide))]
    have leaf := leafWords j (by omega) i
    simpa [a,GroupedBalancedSignBottomStackSlots67.slot,
      node,GroupedBalancedSignBottomTreeModel67.levelNode,
      GroupedBottomTree.root] using leaf
  · intro i
    rw [scratchWords i,shift]
  · rw [preserve 0x81060 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      before 0x81060 (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact maxLevel

#print axioms first_params
#print axioms selected_mask_bound
#print axioms first_start
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStart67
