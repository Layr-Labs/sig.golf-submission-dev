import SigGolfCandidate.Hypertree.SignTreeFinish

/-! Inlined from SigGolfCandidate.Hypertree.SignBottomTreeHelpers; its only importer was SigGolfCandidate.Hypertree.SignBottomTreeLeaves. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure BottomTreeSettings (s : MachineState) (pointer : Nat) (selected : Bool) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selectorEq : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)

def BottomLeafFrame (s final : MachineState) (pointer : Nat) (side : Bool) : Prop :=
  ∀ a, a ≠ 0xffffe0 → a ≠ 0x80430 → a ≠ 0x80438 → OutsideBottomWork side a →
    (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → final.getMem a = s.getMem a

theorem bottomOutside_of_leafResult (side : Bool) (a : Word) (outside : OutsideLeafResult side a) :
    OutsideBottomWork side a := ⟨outside.1.1.1, outside.1.1.2.1, outside.1.1.2.2.1, outside.2.2⟩

theorem BottomLeafFrame.keep (s final : MachineState) (pointer : Nat) (side : Bool)
    (valid : CapturePointerValid pointer) (frame : BottomLeafFrame s final pointer side)
    (a : Word) (stack : a ≠ 0xffffe0) (chain : a ≠ 0x80430) (step : a ≠ 0x80438)
    (outside : OutsideBottomWork side a) (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) :
    final.getMem a = s.getMem a := by
  apply frame a stack chain step outside
  intro i eq
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem treeContext_after_bottom_leaf (s final : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (side : Bool) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey 0 tree)
    (frame : BottomLeafFrame s final pointer side) : TreeContext final secretKey 0 tree := by
  have keep := frame.keep s final pointer side valid
  constructor
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact data.levelEq
  · intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideBottomWork <;> cases side <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> unfold OutsideBottomWork <;> cases side <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem bottomSettings_after_leaf (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (valid : CapturePointerValid pointer) (settings : BottomTreeSettings s pointer selected)
    (frame : BottomLeafFrame s final pointer side) : BottomTreeSettings final pointer selected := by
  have keep := frame.keep s final pointer side valid
  constructor
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.pointerEq
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.enabled
  · rw [keep _ (by decide) (by decide) (by decide) (by unfold OutsideBottomWork; cases side <;> decide) (by decide)]
    exact settings.selectorEq

theorem treeControl_bottom_settings (s : MachineState) (pointer : Nat) (selected : Bool)
    (side : BitVec 12) (jump : BitVec 21) (settings : BottomTreeSettings s pointer selected) :
    BottomTreeSettings (KeygenTreeControl.state s side jump) pointer selected := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.pointerEq
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.enabled
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.selectorEq

theorem treeLeft_bottom_settings (s : MachineState) (pointer : Nat) (selected : Bool)
    (sp : s.getReg .x2 = 0x1000000) (settings : BottomTreeSettings s pointer selected) :
    BottomTreeSettings (treeLeftState s) pointer selected := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.pointerEq
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.enabled
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.selectorEq

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def BottomLowFrame (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat) (side : Bool) : Prop :=
  ∀ a, a.toNat < 0x80000 → final.getMem a =
    if s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 then
      if a = BitVec.ofNat 64 pointer + 8 then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 64 64 else
      if a = BitVec.ofNat 64 pointer then (Reference.secret hash secretKey 0 tree side 0).extractLsb' 0 64 else s.getMem a
    else s.getMem a

theorem bottom_selected_value (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat)
    (side : Bool) (valid : CapturePointerValid pointer) (data : LeafContext s secretKey 0 tree side)
    (settings : BottomTreeSettings s pointer side) (frame : BottomLowFrame s final hash secretKey pointer tree side) :
    CapturedValue final pointer 0 (Reference.secret hash secretKey 0 tree side 0) := by
  have condition : s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 :=
    ⟨settings.enabled, data.leafEq.trans settings.selectorEq.symm⟩
  have ne : BitVec.ofNat 64 pointer ≠ BitVec.ofNat 64 pointer + 8 := by
    intro eq
    have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
    contradiction
  intro i
  have low := signature_word_low pointer valid 0 i
  have h := frame _ low
  rw [if_pos condition] at h
  fin_cases i
  · simpa [wordAddress, ne] using h
  · have addr : wordAddress (pointer+16*(0:Reference.Chain).val) 1 = BitVec.ofNat 64 pointer + 8 := by
      simpa [wordAddress] using BitVec.ofNat_add (n := 64) pointer 8
    rw [addr, if_pos rfl] at h
    rw [addr]
    exact h

theorem bottom_unselected_low (s final : MachineState) (hash : Hash) (secretKey : SecretKey) (pointer tree : Nat)
    (side selected : Bool) (data : LeafContext s secretKey 0 tree side) (settings : BottomTreeSettings s pointer selected)
    (different : side ≠ selected) (frame : BottomLowFrame s final hash secretKey pointer tree side)
    (a : Word) (low : a.toNat < 0x80000) : final.getMem a = s.getMem a := by
  rw [frame a low]
  have ne : s.getMem 0x80428 ≠ s.getMem 0x80420 := by
    rw [data.leafEq, settings.selectorEq]
    cases side <;> cases selected <;> simp_all [Reference.sideNumber]
  simp only [ne, and_false, if_false]

end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Both actual bottom-leaf calls produce their public roots and exactly the selected
secret preimage, before authentication-node copying and the parent hash. -/
theorem sign_bottom_tree_leaves (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer tree : Nat)
    (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (valid : CapturePointerValid pointer)
    (data : TreeContext s secretKey 0 tree) (settings : BottomTreeSettings s pointer selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 4 4 final ∧
      instructions ≤ 430 ∧ cycles ≤ 458 ∧ final.pc = 0x13f8 ∧ final.getReg .x2 = 0xfffff0 ∧
      final.getMem 0xfffff0 = s.getReg .x1 ∧ TreeContext final secretKey 0 tree ∧
      BottomTreeSettings final pointer selected ∧
      (∀ side : Bool, ∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey 0 tree side).extractLsb' (64*i.val) 64) ∧
      CapturedValue final pointer 0 (Reference.secret hash secretKey 0 tree selected 0) ∧
      (∀ a, OutsideTreeLeaves a → (∀ i : Fin 2, a ≠ wordAddress pointer i.val) → final.getMem a = s.getMem a) := by
  let ready := treeLeftState s
  have pre := treeLeft_block s pc sp
  have readyPC := treeLeft_pc s pc
  have readySP := treeLeft_sp s sp
  have readyRA := treeLeft_ra s pc
  have readyContext := treeLeft_context s secretKey 0 tree sp data
  have readySettings := treeLeft_bottom_settings s pointer selected sp settings
  obtain ⟨left, leftSteps, leftCycles, leftTrace, leftStepsBound, leftCyclesBound, leftPC, leftSP, leftRoot,
    leftLow, leftFrame⟩ := sign_bottom_leaf_call hash ready secretKey pointer tree false
      readyPC readySP valid readySettings.pointerEq readyContext
  have leftRet : left.pc = 0x13e4 := by rw [leftPC, readyRA]; decide
  have leftStack : left.getReg .x2 = 0xfffff0 := leftSP.trans readySP
  have readyTree : TreeContext ready secretKey 0 tree := ⟨readyContext.levelEq, readyContext.indexEq, readyContext.secretKeyEq⟩
  have leftContext := treeContext_after_bottom_leaf ready left secretKey pointer tree false valid readyTree leftFrame
  have leftSettings := bottomSettings_after_leaf ready left pointer false selected valid readySettings leftFrame
  let rightReady := KeygenTreeControl.state left 1 344
  have rightPre := KeygenTreeControl.block sign 0x13e4 1 344 sign_tree_right_code left leftRet
  have rightReadyPC : rightReady.pc = 0x154c := by rw [KeygenTreeControl.pc, leftRet]; rfl
  have rightReadySP : rightReady.getReg .x2 = 0xfffff0 := (KeygenTreeControl.sp left 1 344).trans leftStack
  have rightReadyRA : rightReady.getReg .x1 = 0x13f8 := by rw [KeygenTreeControl.ra, leftRet]; rfl
  have rightContext := treeControl_context left secretKey 0 tree true 344 leftContext
  have rightSettings := treeControl_bottom_settings left pointer selected 1 344 leftSettings
  obtain ⟨right, rightSteps, rightCycles, rightTrace, rightStepsBound, rightCyclesBound, rightPC, rightSP, rightRoot,
    rightLow, rightFrame⟩ := sign_bottom_leaf_call hash rightReady secretKey pointer tree true
      rightReadyPC rightReadySP valid rightSettings.pointerEq rightContext
  have rightRet : right.pc = 0x13f8 := by rw [rightPC, rightReadyRA]; decide
  have rightStack : right.getReg .x2 = 0xfffff0 := rightSP.trans rightReadySP
  have rightTree : TreeContext rightReady secretKey 0 tree := ⟨rightContext.levelEq, rightContext.indexEq, rightContext.secretKeyEq⟩
  have finalContext := treeContext_after_bottom_leaf rightReady right secretKey pointer tree true valid rightTree rightFrame
  have finalSettings := bottomSettings_after_leaf rightReady right pointer true selected valid rightSettings rightFrame
  have frame (a : Word) (outside : OutsideTreeLeaves a) (captureOutside : ∀ i : Fin 2, a ≠ wordAddress pointer i.val) :
      right.getMem a = s.getMem a := by
    rw [rightFrame a outside.2.2.2.1 outside.2.1.1.2.1 outside.2.1.1.1.2.2.2
      (bottomOutside_of_leafResult true a outside.2.1) captureOutside,
      KeygenTreeControl.mem, if_neg outside.2.2.1,
      leftFrame a outside.2.2.2.1 outside.1.1.2.1 outside.1.1.1.2.2.2
      (bottomOutside_of_leafResult false a outside.1) captureOutside,
      treeLeft_frame s sp a outside.2.2.2.2 outside.2.2.1]
  have saved : right.getMem 0xfffff0 = s.getReg .x1 := by
    rw [BottomLeafFrame.keep rightReady right pointer true valid rightFrame _ (by decide) (by decide) (by decide)
      (by unfold OutsideBottomWork; decide) (by decide), KeygenTreeControl.mem, if_neg (by decide),
      BottomLeafFrame.keep ready left pointer false valid leftFrame _ (by decide) (by decide) (by decide)
      (by unfold OutsideBottomWork; decide) (by decide), treeLeft_saved s sp]
  refine ⟨right, 12 + leftSteps + rightSteps, 12 + leftCycles + rightCycles, ?_, by omega, by omega,
    rightRet, rightStack, saved, finalContext, finalSettings, ?_, ?_, frame⟩
  · convert pre.trace.trans (leftTrace.trans (rightPre.trace.trans rightTrace)) using 1 <;> omega
  · intro side i
    cases side
    · rw [BottomLeafFrame.keep rightReady right pointer true valid rightFrame _
        (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> unfold OutsideBottomWork <;> decide) (by fin_cases i <;> decide),
        KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
      exact leftRoot i
    · exact rightRoot i
  · cases selected
    · have old := bottom_selected_value ready left hash secretKey pointer tree false valid readyContext readySettings leftLow
      intro i
      have low := signature_word_low pointer valid 0 i
      rw [bottom_unselected_low rightReady right hash secretKey pointer tree true false rightContext rightSettings
        (by decide) rightLow _ low, KeygenTreeControl.mem, if_neg (low_ne_high _ _ low (by decide))]
      exact old i
    · exact bottom_selected_value rightReady right hash secretKey pointer tree true valid rightContext rightSettings rightLow

end SigGolfCandidate.Hypertree.Signing
