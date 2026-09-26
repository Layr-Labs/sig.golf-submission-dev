import SigGolfCandidate.Hypertree.SignBottomTreeFinish
import SigGolfCandidate.Hypertree.SignAdvance
import SigGolfCandidate.Hypertree.LoopIndexArithmetic
import SigGolfCandidate.Hypertree.LoopDispatchFrame

/-! Inlined from SigGolfCandidate.Hypertree.SignTree; its only importer was SigGolfCandidate.Hypertree.SignLayerPrepare. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def LayerStored (s : MachineState) (pointer level : Nat) (signature : Reference.LayerSignature) : Prop :=
  if level = 0 then BottomLayerStored s pointer signature else UpperLayerStored s pointer signature

def layerBytes (level : Nat) : Nat := if level = 0 then 32 else 752

def OutsideLayer (pointer level : Nat) (a : Word) : Prop :=
  a.toNat < pointer ∨ pointer + layerBytes level ≤ a.toNat

theorem outsideLayer_value (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (outside : OutsideLayer pointer level a) (chain : Reference.Chain) (usable : level = 0 → chain.val = 0)
    (i : Fin 2) : a ≠ wordAddress (pointer+16*chain.val) i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have cb := chain.isLt; have ib := i.isLt
  rcases valid with ⟨lower,upper,aligned⟩
  simp only [wordAddress,BitVec.toNat_ofNat] at h
  unfold OutsideLayer layerBytes at outside
  split at outside <;> rename_i hl <;> simp_all <;> omega

theorem outsideLayer_sibling (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (outside : OutsideLayer pointer level a) (i : Fin 2) :
    a ≠ wordAddress (pointer + (if level = 0 then 16 else 736)) i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  have ib := i.isLt
  rcases valid with ⟨lower,upper,aligned⟩
  simp only [wordAddress,BitVec.toNat_ofNat] at h
  unfold OutsideLayer layerBytes at outside
  split at outside <;> rename_i hl <;> simp_all <;> omega

/-- Both signer tree paths produce exactly the reference layer's serialized fields. -/
theorem sign_tree (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (message : Reference.Digest) (selected : Bool) (pc : s.pc = 0x13c8) (sp : s.getReg .x2 = 0x1000000)
    (bound : level < 160) (valid : CapturePointerValid pointer) (data : TreeContext s secretKey level tree)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer) (enabled : s.getMem 0x80440 ≠ 0)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber selected))
    (digits : level ≠ 0 → ∀ chain : Reference.Chain,
      s.getByte (BitVec.ofNat 64 (0x80600+chain.val)) = BitVec.ofNat 8 (Reference.digit message chain).val) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles
      (if level = 0 then 5 else 739) (if level = 0 then 5 else 761) final ∧
      instructions ≤ (if level = 0 then 537 else 99910) ∧ cycles ≤ (if level = 0 then 572 else 105259) ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.treeRoot hash secretKey level tree).extractLsb' (64*i.val) 64) ∧
      LayerStored final pointer level (Reference.signLayer hash secretKey level tree selected message) ∧
      (∀ a, OutsideTreeWork a → OutsideLayer pointer level a → final.getMem a = s.getMem a) := by
  by_cases zero : level = 0
  · subst level
    obtain ⟨final,n,c,run,nb,cb,fpc,fsp,root,stored,frame⟩ :=
      sign_bottom_tree hash s secretKey pointer tree selected pc sp valid data ⟨ptr,enabled,selector⟩
    refine ⟨final,n,c,run,nb,cb,fpc,fsp,root,?_,?_⟩
    · simpa [LayerStored,BottomLayerStored,Reference.signLayer] using stored
    · intro a work outside
      apply frame a work
      · intro i
        simpa using outsideLayer_value pointer 0 valid a outside 0 (by simp) i
      · exact fun i => outsideLayer_sibling pointer 0 valid a outside i
  · have wordNonzero : BitVec.ofNat 64 level ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change level % 2^64 = 0 at h
      omega
    obtain ⟨final,n,c,run,nb,cb,fpc,fsp,root,stored,frame⟩ :=
      sign_upper_tree hash s secretKey pointer level tree message selected pc sp wordNonzero valid data
        ⟨ptr,enabled,selector,digits zero⟩
    refine ⟨final,n,c,?_,?_,?_,fpc,fsp,root,?_,?_⟩
    · simpa only [if_neg zero] using run
    · simpa only [if_neg zero] using nb
    · simpa only [if_neg zero] using cb
    · simpa only [LayerStored,if_neg zero] using stored
    · intro a work outside
      apply frame a work
      · exact fun chain i => outsideLayer_value pointer level valid a outside chain (by simp [zero]) i
      · intro i
        simpa only [if_neg zero] using outsideLayer_sibling pointer level valid a outside i

/-- Low memory is untouched by the tree's scratch work. -/
theorem outsideTreeWork_low (a : Word) (low : a.toNat < 0x80000) : OutsideTreeWork a := by
  have ne (b : Word) (high : 0x80000 ≤ b.toNat) : a ≠ b := low_ne_high a b low high
  refine ⟨⟨outsideLeaf_regions false a (Or.inl low) (ne _ (by decide)) (ne _ (by decide)),
    outsideLeaf_regions true a (Or.inl low) (ne _ (by decide)) (ne _ (by decide)),
    ne _ (by decide),ne _ (by decide),ne _ (by decide)⟩,(low_outside_node a low).2.2⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_tree
end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

structure LoopData (s : MachineState) (secretKey : SecretKey) (level index : Nat) (current : Reference.Digest) : Prop where
  stack : s.getReg .x2 = 0x1000000
  counter : s.getMem 0x80400 = BitVec.ofNat 64 level
  indexWords : StoredIndex s (BitVec.ofNat 192 index)
  secretKeyWords : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64
  mode : s.getMem 0x80440 = 1
  pointer : s.getMem 0x80448 = BitVec.ofNat 64 (0x20060+layerOffset level)
  currentWords : ∀ i : Fin 2, s.getMem (wordAddress 0x80500 i.val) = current.extractLsb' (64*i.val) 64

theorem sign_pointer_valid (level : Nat) (bound : level < 160) :
    CapturePointerValid (0x20060+layerOffset level) := by
  refine ⟨?_,?_,layer_pointer_aligned _ _ (by decide)⟩
  all_goals unfold layerOffset; split <;> omega

theorem shift_word_frame (s : MachineState) (a : Word)
    (h1 : a ≠ 0x80418) (h2 : a ≠ 0x80410) (h3 : a ≠ 0x80408) (h4 : a ≠ 0x80420) :
    (shiftIndexState s).getMem a = s.getMem a := by
  rw [shiftIndexState_mem,if_neg h1,if_neg h2,if_neg h3,if_neg h4]

/-- One loop's index shift and optional encoding arrive at the actual tree entry. -/
theorem sign_layer_prepare (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level index : Nat)
    (current : Reference.Digest) (pc : s.pc = 0x1220) (bound : level < 160) (small : index < 2^192)
    (data : LoopData s secretKey level index current) :
    ∃ ready, Trace hash sign s
      (if level = 0 then 34 else if Reference.needsFlip current then 526 else 494)
      (if level = 0 then 34 else if Reference.needsFlip current then 526 else 494) 0 0 ready ∧
      ready.pc = 0x13c8 ∧ ready.getReg .x1 = 0x12ac ∧ ready.getReg .x2 = 0x1000000 ∧
      TreeContext ready secretKey level (index/2) ∧
      ready.getMem 0x80448 = BitVec.ofNat 64 (0x20060+layerOffset level) ∧ ready.getMem 0x80440 = 1 ∧
      ready.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber (index%2==1)) ∧
      (level ≠ 0 → ∀ chain : Reference.Chain,
        ready.getByte (BitVec.ofNat 64 (0x80600+chain.val)) = BitVec.ofNat 8 (Reference.digit current chain).val) ∧
      (∀ address : Nat, address < 0x80000 → address%8=0 →
        ready.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) := by
  let shifted := shiftIndexState s
  have shiftRun := shiftIndexState_block s pc
  have shiftedPC : shifted.pc = 0x1294 := by rw [shiftIndexState_pc,pc]; rfl
  have shiftedSP : shifted.getReg .x2 = 0x1000000 := (shiftIndexState_sp s).trans data.stack
  have shiftedLevel : shifted.getMem 0x80400 = BitVec.ofNat 64 level := by
    rw [shift_word_frame s _ (by decide) (by decide) (by decide) (by decide)]; exact data.counter
  have coordinates := shift_index_nat s index small data.indexWords
  have currentLo : shifted.getMem 0x80500 = current.extractLsb' 0 64 := by
    rw [shift_word_frame s _ (by decide) (by decide) (by decide) (by decide)]; exact data.currentWords 0
  have currentHi : shifted.getMem 0x80508 = current.extractLsb' 64 64 := by
    rw [shift_word_frame s _ (by decide) (by decide) (by decide) (by decide)]; exact data.currentWords 1
  obtain ⟨ready,dispatch,readyPC,readyRA,readySP,digits,frame⟩ :=
    dispatch_to_tree sign 0x1294 sign_dispatch_code sign_encode_code (by decide) shifted current shiftedPC shiftedSP currentLo currentHi
  have keep (address : Nat) (aligned : address%8=0) (small : address+8<2^64)
      (separate : address+8≤0x80600 ∨ 0x80630≤address) (saved : address≠0xfffff0) :
      ready.getMem (BitVec.ofNat 64 address) = shifted.getMem (BitVec.ofNat 64 address) :=
    dispatch_frame_words shifted ready shiftedSP frame address aligned small separate saved
  have combined (address : Nat) (aligned : address%8=0) (small : address+8<2^64)
      (separate : address+8≤0x80600 ∨ 0x80630≤address) (saved : address≠0xfffff0)
      (h1 : BitVec.ofNat 64 address ≠ 0x80418) (h2 : BitVec.ofNat 64 address ≠ 0x80410)
      (h3 : BitVec.ofNat 64 address ≠ 0x80408) (h4 : BitVec.ofNat 64 address ≠ 0x80420) :
      ready.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) := by
    rw [keep address aligned small separate saved,shift_word_frame s _ h1 h2 h3 h4]
  have zero : shifted.getMem 0x80400 = 0 ↔ level = 0 := by rw [shiftedLevel]; exact level_word_zero level bound
  refine ⟨ready,?_,readyPC,readyRA,readySP.trans shiftedSP,?_,?_,?_,?_,?_,?_⟩
  · have run := shiftRun.trace (hash := hash) |>.trans dispatch.trace
    by_cases h : level = 0
    · simpa only [zero, h, if_true, Nat.reduceAdd] using run
    · by_cases flip : Reference.needsFlip current
      · simpa only [zero, h, flip, if_true, if_false, Nat.reduceAdd] using run
      · simpa only [zero, h, flip, if_true, if_false, Nat.reduceAdd] using run
  · constructor
    · exact (keep 0x80400 (by decide) (by decide) (by decide) (by decide)).trans shiftedLevel
    · intro i
      rw [show wordAddress 0x80408 i.val = BitVec.ofNat 64 (0x80408+8*i.val) by rfl,
        keep _ (by omega) (by have := i.isLt; omega) (by have := i.isLt; omega) (by have := i.isLt; omega)]
      exact coordinates.1 i
    · intro i
      rw [show wordAddress 0x20 i.val = BitVec.ofNat 64 (0x20+8*i.val) by rfl,
        combined _ (by omega) (by have := i.isLt; omega) (by have := i.isLt; omega)
        (by have := i.isLt; omega) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact data.secretKeyWords i
  · exact (combined 0x80448 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans data.pointer
  · exact (combined 0x80440 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans data.mode
  · exact (keep 0x80420 (by decide) (by decide) (by decide) (by decide)).trans coordinates.2
  · intro nonzero; exact digits (fun h => nonzero (zero.mp h))
  · intro address low aligned
    apply combined address aligned (by omega) (by omega) (by omega)
    all_goals apply low_ne_high _ _ (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)] using low) (by decide)

end SigGolfCandidate.Hypertree.Signing
