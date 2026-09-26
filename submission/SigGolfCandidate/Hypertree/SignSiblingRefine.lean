import SigGolfCandidate.Hypertree.SignLeafCall
import SigGolfCandidate.Hypertree.SignSiblingRun
import SigGolfCandidate.Hypertree.KeygenTreeControl

/-! Inlined from SigGolfCandidate.Hypertree.SignTreeHelpers; its only importer was SigGolfCandidate.Hypertree.SignSiblingRefine. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure TreeSettings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selectorEq : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)
  digits : ∀ chain : Reference.Chain,
    s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val

theorem TreeSettings.selected (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (settings : TreeSettings s pointer message selected)
    (data : LeafContext s secretKey level tree selected) : LeafSignatureSettings s pointer message := by
  intro chain
  exact ⟨settings.pointerEq, settings.enabled, data.leafEq.trans settings.selectorEq.symm, settings.digits chain⟩

theorem TreeSettings.unselected (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (side selected : Bool) (settings : TreeSettings s pointer message selected)
    (data : LeafContext s secretKey level tree side) (different : side ≠ selected) :
    s.getMem 0x80428 ≠ s.getMem 0x80420 := by
  rw [data.leafEq, settings.selectorEq]
  cases side <;> cases selected <;> simp_all [Reference.sideNumber]

/-- Uniform upper-leaf call interface, with signature output exactly when this leaf is selected. -/
theorem sign_upper_leaf_call (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side selected : Bool) (message : Reference.Digest) (pc : s.pc = 0x154c) (sp : s.getReg .x2 = 0xfffff0)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafContext s secretKey level tree side) (settings : TreeSettings s pointer message selected) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 369 380 final ∧
      instructions ≤ 49895 ∧ cycles ≤ 52566 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.leafRoot hash secretKey level tree side).extractLsb' (64*i.val) 64) ∧
      (side = selected → SignatureBefore final hash secretKey pointer level tree side message 46) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a →
        (side = selected → ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) →
          final.getMem a = s.getMem a) := by
  by_cases same : side = selected
  · subst side
    obtain ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, signature, frame⟩ :=
      sign_selected_leaf_call hash s secretKey pointer level tree selected message pc sp nonzero valid data
        (settings.selected s secretKey pointer level tree message selected data)
    exact ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, fun _ => signature,
      fun a stack outside capture => frame a stack outside (capture rfl)⟩
  · obtain ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, frame⟩ :=
      sign_unselected_leaf_call hash s secretKey pointer level tree side pc sp nonzero valid data settings.pointerEq
        (settings.unselected s secretKey pointer level tree message side selected data same)
    exact ⟨final, steps, cycles, trace, hs, hc, fpc, fsp, root, fun eq => (same eq).elim,
      fun a stack outside _ => frame a stack outside⟩

theorem sign_tree_left_code : KeygenTreeControl.Code sign 0x13d0 0 364 := by decide
theorem sign_tree_right_code : KeygenTreeControl.Code sign 0x13e4 1 344 := by decide

end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

structure TreeContext (s : MachineState) (secretKey : SecretKey) (level tree : Nat) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyEq : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64

def SignatureWordsOutside (pointer : Nat) (a : Word) : Prop :=
  ∀ chain : Reference.Chain, ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val

def UpperLeafFrame (s final : MachineState) (pointer : Nat) (side selected : Bool) : Prop :=
  ∀ a, a ≠ 0xffffe0 → OutsideLeafResult side a →
    (side = selected → SignatureWordsOutside pointer a) → final.getMem a = s.getMem a

theorem signatureWordsOutside_range (pointer : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : SignatureWordsOutside pointer a := by
  intro chain i eq
  have cb := chain.isLt
  have ib := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

/-- Regions unchanged by a leaf body, including metadata, input, digits, and stack. -/
theorem outsideLeaf_regions (side : Bool) (a : Word)
    (region : a.toNat < 0x80000 ∨ (0x80400 ≤ a.toNat ∧ a.toNat < 0x80510) ∨
      (0x80600 ≤ a.toNat ∧ a.toNat < 0x80800) ∨ 0x80ae0 ≤ a.toNat)
    (chain : a ≠ 0x80430) (step : a ≠ 0x80438) : OutsideLeafResult side a := by
  refine ⟨⟨⟨?_, ?_, ?_, step⟩, chain, ?_⟩, ?_, ?_⟩
  all_goals (first | intro c i eq | intro i eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals cases side <;> simp [wordAddress, KeygenEndpoint.endpointAddress,
    KeygenSavePublic.wordAddress, Reference.sideNumber] at h <;> omega

theorem UpperLeafFrame.keep (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (valid : CapturePointerValid pointer) (frame : UpperLeafFrame s final pointer side selected)
    (a : Word) (stack : a ≠ 0xffffe0) (outside : OutsideLeafResult side a)
    (range : a.toNat < 0x20060 ∨ 0x80000 ≤ a.toNat) : final.getMem a = s.getMem a :=
  frame a stack outside (fun _ => signatureWordsOutside_range pointer valid a range)

theorem treeContext_after_leaf (s final : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side selected : Bool) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey level tree)
    (frame : UpperLeafFrame s final pointer side selected) : TreeContext final secretKey level tree := by
  have keep := frame.keep s final pointer side selected valid
  constructor
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact data.levelEq
  · intro i
    rw [keep _ (by fin_cases i <;> decide)
      (outsideLeaf_regions side _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [keep _ (by fin_cases i <;> decide)
      (outsideLeaf_regions side _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide))
      (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeSettings_after_leaf (s final : MachineState) (pointer : Nat) (side selected : Bool)
    (message : Reference.Digest) (valid : CapturePointerValid pointer) (settings : TreeSettings s pointer message selected)
    (frame : UpperLeafFrame s final pointer side selected) : TreeSettings final pointer message selected := by
  have keep := frame.keep s final pointer side selected valid
  constructor
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.pointerEq
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.enabled
  · rw [keep _ (by decide) (outsideLeaf_regions side _ (by decide) (by decide) (by decide)) (by decide)]
    exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word final 0x80600 chain.val (by decide) (by omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · intro eq; have h := congrArg BitVec.toNat eq; simp [wordAddress] at h; omega
    · apply outsideLeaf_regions side
      · simp only [wordAddress, BitVec.toNat_ofNat]; omega
      all_goals intro eq
      all_goals have h := congrArg BitVec.toNat eq
      all_goals simp [wordAddress] at h
      all_goals omega
    · simp only [wordAddress, BitVec.toNat_ofNat]; omega

theorem treeControl_context (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (jump : BitVec 21)
    (data : TreeContext s secretKey level tree) :
    LeafContext (KeygenTreeControl.state s (BitVec.ofNat 12 (Reference.sideNumber side)) jump) secretKey level tree side := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact data.levelEq
  · rw [KeygenTreeControl.mem, if_pos rfl]; cases side <;> rfl
  · intro i
    rw [KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [KeygenTreeControl.mem, if_neg (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeControl_settings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool)
    (side : BitVec 12) (jump : BitVec 21) (settings : TreeSettings s pointer message selected) :
    TreeSettings (KeygenTreeControl.state s side jump) pointer message selected := by
  constructor
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.pointerEq
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.enabled
  · rw [KeygenTreeControl.mem, if_neg (by decide)]; exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word _ 0x80600 chain.val (by decide) (by omega), KeygenTreeControl.mem, if_neg]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · intro eq; have h := congrArg BitVec.toNat eq; simp [wordAddress] at h; omega

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- The tree entry saves its caller and selects the left leaf before calling it. -/
def treeLeftState (s : MachineState) : MachineState := KeygenTreeControl.state (enterState s) 0 364

theorem treeLeft_frame (s : MachineState) (sp : s.getReg .x2 = 0x1000000)
    (a : Word) (stack : a ≠ 0xfffff0) (leaf : a ≠ 0x80428) :
    (treeLeftState s).getMem a = s.getMem a := by
  rw [treeLeftState, KeygenTreeControl.mem, if_neg leaf, enter_mem, sp, if_neg (by simpa using stack)]

theorem treeLeft_block (s : MachineState) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000) :
    OrdinarySteps sign s 7 (treeLeftState s) := by
  have enter := enter_block sign 0x13c8 sign_tree_enter_code s pc (by rw [sp]; decide)
  have epc : (enterState s).pc = 0x13d0 := by rw [enter_pc, pc]; rfl
  have call := KeygenTreeControl.block sign 0x13d0 0 364 sign_tree_left_code (enterState s) epc
  exact ordinary_trans sign s _ _ 2 5 enter call

theorem treeLeft_pc (s : MachineState) (pc : s.pc = 0x13c8) : (treeLeftState s).pc = 0x154c := by
  rw [treeLeftState, KeygenTreeControl.pc, enter_pc, pc]; rfl

theorem treeLeft_ra (s : MachineState) (pc : s.pc = 0x13c8) : (treeLeftState s).getReg .x1 = 0x13e4 := by
  rw [treeLeftState, KeygenTreeControl.ra, enter_pc, pc]; rfl

theorem treeLeft_sp (s : MachineState) (sp : s.getReg .x2 = 0x1000000) : (treeLeftState s).getReg .x2 = 0xfffff0 := by
  rw [treeLeftState, KeygenTreeControl.sp, enter_sp, sp]; rfl

theorem treeLeft_saved (s : MachineState) (sp : s.getReg .x2 = 0x1000000) :
    (treeLeftState s).getMem 0xfffff0 = s.getReg .x1 := by
  rw [treeLeftState, KeygenTreeControl.mem, if_neg (by decide), enter_mem, sp, if_pos (by decide)]

theorem treeLeft_context (s : MachineState) (secretKey : SecretKey) (level tree : Nat)
    (sp : s.getReg .x2 = 0x1000000) (data : TreeContext s secretKey level tree) :
    LeafContext (treeLeftState s) secretKey level tree false := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact data.levelEq
  · rw [treeLeftState, KeygenTreeControl.mem, if_pos rfl]; rfl
  · intro i
    rw [treeLeft_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.indexEq i
  · intro i
    rw [treeLeft_frame s sp _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact data.secretKeyEq i

theorem treeLeft_settings (s : MachineState) (pointer : Nat) (message : Reference.Digest) (selected : Bool)
    (sp : s.getReg .x2 = 0x1000000) (settings : TreeSettings s pointer message selected) :
    TreeSettings (treeLeftState s) pointer message selected := by
  constructor
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.pointerEq
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.enabled
  · rw [treeLeft_frame s sp _ (by decide) (by decide)]; exact settings.selectorEq
  · intro chain
    have cb := chain.isLt
    rw [getByte_word _ 0x80600 chain.val (by decide) (by omega), treeLeft_frame]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by omega)]
      exact settings.digits chain
    · exact sp
    all_goals intro eq
    all_goals have h := congrArg BitVec.toNat eq
    all_goals simp [wordAddress] at h
    all_goals omega

end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem sibling_source_eq (s : MachineState) (selected : Bool)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected)) :
    siblingSource s = KeygenSavePublic.wordAddress (!selected) 0 ∧
      siblingSource s + 8 = KeygenSavePublic.wordAddress (!selected) 1 := by
  unfold siblingSource
  rw [selector]
  cases selected <;> constructor <;> rfl

theorem sibling_upper_destination (s : MachineState) (pointer : Nat)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (nonzero : s.getMem 0x80400 ≠ 0) :
    siblingDestination s = BitVec.ofNat 64 (pointer + 736) := by
  rw [siblingDestination, if_neg nonzero, ptr]
  exact (BitVec.ofNat_add _ _).symm

theorem sibling_upper_safe (pointer : Nat) (valid : CapturePointerValid pointer) :
    accessValid (BitVec.ofNat 64 (pointer + 736)) 8 = true ∧
    accessValid (BitVec.ofNat 64 (pointer + 736) + 8) 8 = true := by
  rcases valid with ⟨lower, upper, aligned⟩
  simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_add]
  omega

def SiblingStored (s : MachineState) (pointer : Nat) (value : Reference.Digest) : Prop :=
  ∀ i : Fin 2, s.getMem (wordAddress (pointer + 736) i.val) = value.extractLsb' (64*i.val) 64

/-- The actual enabled upper-layer sibling path copies the opposite public leaf root to
the authentication-node slot. All other words, including the signature vector, are framed. -/
theorem sign_upper_sibling (s : MachineState) (pointer : Nat) (selected : Bool) (value : Reference.Digest)
    (pc : s.pc = 0x13f8) (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (enabled : s.getMem 0x80440 ≠ 0)
    (nonzero : s.getMem 0x80400 ≠ 0)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected))
    (words : ∀ i : Fin 2, s.getMem (KeygenSavePublic.wordAddress (!selected) i.val) = value.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps sign s 25 final ∧ final.pc = 0x1460 ∧
      SiblingStored final pointer value ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, (∀ i : Fin 2, a ≠ wordAddress (pointer + 736) i.val) → final.getMem a = s.getMem a) := by
  let ready := captureModeState 92 s
  have mode := captureMode_block sign 0x13f8 92 sign_sibling_mode_code s pc
  have readyPC : ready.pc = 0x1408 := by rw [captureMode_pc, if_neg enabled, pc]; rfl
  have readyNonzero : ready.getMem 0x80400 ≠ 0 := by simpa only [ready, captureMode_mem] using nonzero
  have readyPointer : ready.getMem 0x80448 = BitVec.ofNat 64 pointer := by simpa only [ready, captureMode_mem] using ptr
  have readySelector : ready.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected) := by simpa only [ready, captureMode_mem] using selector
  have source := sibling_source_eq ready selected readySelector
  have destination := sibling_upper_destination ready pointer readyPointer readyNonzero
  have safe := sibling_upper_safe pointer valid
  have copy := sibling_block sign 0x1408 sign_sibling_code ready readyPC
    (by rw [source.1]; cases selected <;> decide)
    (by rw [source.2]; cases selected <;> decide)
    (by rw [destination]; exact safe.1) (by rw [destination]; exact safe.2)
  rw [if_neg readyNonzero] at copy
  refine ⟨siblingState ready, ordinary_trans sign s ready _ 4 21 mode copy,
    siblingState_pc ready 0x1408 readyPC, ?_, (siblingState_sp ready).trans (captureMode_sp 92 s), ?_⟩
  · intro i
    rw [siblingState_mem, destination, source.2, source.1]
    have next : wordAddress (pointer+736) 1 = BitVec.ofNat 64 (pointer+736) + 8 := BitVec.ofNat_add _ _
    have ne : BitVec.ofNat 64 (pointer+736) ≠ BitVec.ofNat 64 (pointer+736) + 8 := by
      intro eq
      have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
      contradiction
    fin_cases i
    · change (if BitVec.ofNat 64 (pointer+736) = BitVec.ofNat 64 (pointer+736) + 8 then _ else _) = _
      rw [if_neg ne]
      simpa [wordAddress, ready, captureMode_mem] using words 0
    · rw [next, if_pos rfl, captureMode_mem]
      exact words 1
  · intro a outside
    rw [siblingState_mem, destination, source.2, source.1]
    have zero : a ≠ BitVec.ofNat 64 (pointer+736) := outside 0
    have one : a ≠ BitVec.ofNat 64 (pointer+736) + 8 := by simpa [wordAddress, BitVec.ofNat_add] using outside 1
    rw [if_neg one, if_neg zero, captureMode_mem]

end SigGolfCandidate.Hypertree.Signing
