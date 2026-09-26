import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedLevels67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStartStack67

/-! The bottom-tree entry preserves the selected ten-bit index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem start_selected (hash : Hash) (secretKey : SecretKey)
    (base selectedIndex : Nat) (s : MachineState)
    (pc : s.pc = 0x14ec)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700)
    (aligned : base % 1024 = 0)
    (bounded : base + 1024 ≤ 2^160)
    (count : s.getMem 0x810d0 = 1024)
    (height : s.getMem 0x81000 = 0)
    (maxLevel : s.getMem 0x81060 = 10)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex)
    (selectedBound : selectedIndex < 1024)
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
      Start hash secretKey base 0 512 0x83000 0x88000 (base/2) t ∧
      (t.getMem 0x810e8).toNat = selectedIndex ∧
      t.getReg .x2 = s.getReg .x2 - 16 ∧
      t.getMem (s.getReg .x2 - 16) = 0x14f0 ∧
      (∀ a, Protected a → a ≠ s.getReg .x2 - 16 →
        t.getMem a = s.getMem a) := by
  have selectedSmall : (s.getMem 0x810e8).toNat<1024 := by
    rw [selectedWord]
    exact selectedBound
  obtain ⟨t,run,params,start,stack,saved,protectedFrame⟩ :=
    GroupedBalancedSignBottomTreeStartStack67.start_stack hash secretKey
      base s pc sp aligned bounded count height maxLevel witnessBase
      selectedSmall scratch leafWords
  let called := GroupedBalancedSignBottomTreeCall67.callState s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let prepared := GroupedBalancedSignBottomTreeInit67.initState entered
  let shifted := GroupedBalancedSignBottomTreeIndexData67.fullState prepared
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
  have copySelected : other.getMem 0x810e8 = shifted.getMem 0x810e8 := by
    apply copyFrame
    intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases cases with h | h | h
    · subst i; decide
    · subst i; decide
    · subst i; decide
  have shiftSelected : shifted.getMem 0x810e8 = prepared.getMem 0x810e8 :=
    GroupedBalancedSignBottomTreeIndexData67.shift_frame prepared 0x810e8
      (by decide) (by decide) (by decide)
  have initSelected : prepared.getMem 0x810e8 = entered.getMem 0x810e8 :=
    GroupedBalancedSignBottomTreeInitData67.init_frame entered 0x810e8
      (by decide) (by decide) (by decide)
  have slotNe : called.getReg .x2 - 16 ≠ 0x810e8 := by
    rcases callSp with h | h <;> rw [h] <;> decide
  have entrySelected : entered.getMem 0x810e8 = called.getMem 0x810e8 :=
    GroupedBalancedSignBottomTreeEntryData67.entry_frame called 0x810e8
      (Ne.symm slotNe) (by decide)
  have callSelected : called.getMem 0x810e8 = s.getMem 0x810e8 :=
    GroupedBalancedSignBottomTreeCall67.call_mem s 0x810e8
  have preserved : t.getMem 0x810e8 = s.getMem 0x810e8 := by
    rw [same,copySelected,shiftSelected,initSelected,entrySelected,callSelected]
  refine ⟨t,run,params,start,?_,stack,saved,protectedFrame⟩
  rw [preserved]
  exact selectedWord

#print axioms start_selected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedEntry67
