import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStart67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllStack67
import SigGolfCandidate.TraceDeterminism

/-! The first parent state has the saved return link at the actual stack slot. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStartStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentProtected67
open GroupedBalancedSignBottomTreeLevelProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem start_stack (hash : Hash) (secretKey : SecretKey)
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
        base 0 512 0x83000 0x88000 (base/2) t ∧
      t.getReg .x2 = s.getReg .x2 - 16 ∧
      t.getMem (s.getReg .x2 - 16) = 0x14f0 ∧
      (∀ a, Protected a → a ≠ s.getReg .x2 - 16 →
        t.getMem a = s.getMem a) := by
  obtain ⟨t,run,params,start⟩ :=
    GroupedBalancedSignBottomTreeStart67.first_start hash secretKey base s
      pc sp aligned bounded count height maxLevel witnessBase selectedBound
      scratch leafWords
  let called := GroupedBalancedSignBottomTreeCall67.callState s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let prepared := GroupedBalancedSignBottomTreeInit67.initState entered
  have callTrace := GroupedBalancedSignBottomTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignBottomTreeCall67.call_pc s pc
  have callSp : called.getReg .x2 = 0xfff7e0 ∨ called.getReg .x2 = 0xfff700 := by
    rw [GroupedBalancedSignBottomTreeCall67.call_stack]
    exact sp
  have entryTrace := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc callSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initTrace := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  let shifted := GroupedBalancedSignBottomTreeIndexData67.fullState prepared
  have shiftTrace := GroupedBalancedSignBottomTreeIndexData67.full_steps prepared initPc
  have shiftPc := GroupedBalancedSignBottomTreeIndexData67.full_pc prepared initPc
  obtain ⟨other,copyTrace,_,_,copyFrame⟩ :=
    GroupedBalancedSignBottomTreeHeaderCopy67.header_copy shifted shiftPc
  have prelude : OrdinarySteps image prepared 48 other := by
    simpa only [show 25+23=48 by decide] using
      Keygen.ordinary_trans image prepared shifted other 25 23
        shiftTrace copyTrace
  have constructed : Trace hash image s 72 72 0 0 other := by
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (((OrdinarySteps.trace (hash := hash) callTrace).trans
        (OrdinarySteps.trace (hash := hash) entryTrace)).trans
        (OrdinarySteps.trace (hash := hash) initTrace)).trans
        (OrdinarySteps.trace (hash := hash) prelude)
  have same := Trace.deterministic run constructed
  have initSp : prepared.getReg .x2 = entered.getReg .x2 := by
    simp [prepared,GroupedBalancedSignBottomTreeInit67.initState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have fullSp : t.getReg .x2 = s.getReg .x2 - 16 := by
    rw [same]
    exact (GroupedBalancedSignBottomTreeLevelStack67.prelude_sp
      prepared other initPc prelude).trans
      (initSp.trans ((GroupedBalancedSignBottomTreeEntryData67.entry_stack called).trans
        (by rw [GroupedBalancedSignBottomTreeCall67.call_stack])))
  have slotHigh : 0x90000 ≤ (s.getReg .x2 - 16).toNat := by
    rcases sp with h | h <;> rw [h] <;> decide
  have enteredSlot : entered.getMem (s.getReg .x2 - 16) = 0x14f0 := by
    have separate : called.getReg .x2 - 16 ≠ 0x81050 := by
      rcases callSp with h | h <;> rw [h] <;> decide
    have saved := GroupedBalancedSignBottomTreeEntryData67.entry_saved_link
      called separate
    rw [GroupedBalancedSignBottomTreeCall67.call_stack] at saved
    exact saved.trans (GroupedBalancedSignBottomTreeCall67.call_link s pc)
  have protected_frame (a : Word) (safe : Protected a) :
      other.getMem a = prepared.getMem a := by
    have ne0 : a ≠ 0x81008 := protected_ne a safe 0x81008 (by decide) (by decide) (by decide) (by decide)
    have ne1 : a ≠ 0x81010 := protected_ne a safe 0x81010 (by decide) (by decide) (by decide) (by decide)
    have ne2 : a ≠ 0x81018 := protected_ne a safe 0x81018 (by decide) (by decide) (by decide) (by decide)
    rw [copyFrame a (by
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases cases with h | h | h
      · subst i; simpa [Signing.wordAddress] using ne0
      · subst i; simpa [Signing.wordAddress] using ne1
      · subst i; simpa [Signing.wordAddress] using ne2)]
    apply GroupedBalancedSignBottomTreeIndexData67.shift_frame
    all_goals exact protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have initFrame (a : Word) (safe : Protected a) :
      prepared.getMem a = entered.getMem a := by
    apply GroupedBalancedSignBottomTreeInitData67.init_frame
    all_goals exact protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have entryFrame (a : Word) (safe : Protected a)
      (neSlot : a ≠ s.getReg .x2 - 16) :
      entered.getMem a = s.getMem a := by
    have neLevel : a ≠ 0x81050 :=
      protected_ne a safe 0x81050 (by decide) (by decide) (by decide) (by decide)
    have frame := GroupedBalancedSignBottomTreeEntryData67.entry_frame
      called a (by rw [GroupedBalancedSignBottomTreeCall67.call_stack]; exact neSlot)
        neLevel
    exact frame.trans (GroupedBalancedSignBottomTreeCall67.call_mem s a)
  have slotProtected : Protected (s.getReg .x2 - 16) := Or.inl slotHigh
  have saved : t.getMem (s.getReg .x2 - 16) = 0x14f0 := by
    rw [same,protected_frame _ slotProtected,initFrame _ slotProtected]
    exact enteredSlot
  refine ⟨t,run,params,start,fullSp,saved,?_⟩
  intro a safe neSlot
  rw [same,protected_frame a safe,initFrame a safe]
  exact entryFrame a safe neSlot

#print axioms start_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStartStack67
