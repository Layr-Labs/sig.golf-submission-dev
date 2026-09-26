import SigGolfCandidate.Hypertree.SignLayerPrepare

/-! Inlined from SigGolfCandidate.Hypertree.SignLayer; its only importer was SigGolfCandidate.Hypertree.SignLayersMemory. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

theorem outsideTreeWork_metadata (a : Word)
    (range : (0x80400 ≤ a.toNat ∧ a.toNat < 0x80428) ∨ (0x80440 ≤ a.toNat ∧ a.toNat < 0x80450)) :
    OutsideTreeWork a := by
  have chain : a ≠ 0x80430 := by intro eq; rw [eq] at range; revert range; decide
  have step : a ≠ 0x80438 := by intro eq; rw [eq] at range; revert range; decide
  refine ⟨⟨outsideLeaf_regions false a (by omega) chain step,
    outsideLeaf_regions true a (by omega) chain step,?_,?_,?_⟩,?_⟩
  · intro eq; rw [eq] at range; revert range; decide
  · intro eq; rw [eq] at range; revert range; decide
  · intro eq; rw [eq] at range; revert range; decide
  · intro i eq
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress,BitVec.toNat_ofNat] at h
    have := i.isLt
    omega

theorem outsideLayer_high (pointer level : Nat) (valid : CapturePointerValid pointer) (a : Word)
    (high : 0x80000 ≤ a.toNat) : OutsideLayer pointer level a := by
  rcases valid with ⟨lower,upper,aligned⟩
  right
  unfold layerBytes
  split <;> omega

theorem advance_low_frame (s : MachineState) (a : Word) (low : a.toNat < 0x80000) :
    (advanceState s).getMem a = s.getMem a := by
  rw [advanceState_mem,if_neg (low_ne_high _ _ low (by decide)),if_neg (low_ne_high _ _ low (by decide))]

theorem LayerStored.frame (s final : MachineState) (pointer level : Nat) (signature : Reference.LayerSignature)
    (valid : CapturePointerValid pointer) (stored : LayerStored s pointer level signature)
    (frame : ∀ a, a.toNat < 0x80000 → final.getMem a = s.getMem a) : LayerStored final pointer level signature := by
  unfold LayerStored at *
  split at stored <;> rename_i h
  all_goals simp only [h,if_true,if_false]
  · constructor
    · intro i
      rw [frame _ (signature_word_low pointer valid 0 i)]
      exact stored.1 i
    · intro i
      have low : (wordAddress (pointer+16) i.val).toNat < 0x80000 := by
        rcases valid with ⟨lower,upper,aligned⟩
        have := i.isLt
        simp only [wordAddress,BitVec.toNat_ofNat]; omega
      rw [frame _ low]; exact stored.2 i
  · constructor
    · intro chain i
      rw [frame _ (signature_word_low pointer valid chain i)]; exact stored.1 chain i
    · intro i
      have low : (wordAddress (pointer+736) i.val).toNat < 0x80000 := by
        rcases valid with ⟨lower,upper,aligned⟩
        have := i.isLt
        simp only [wordAddress,BitVec.toNat_ofNat]; omega
      rw [frame _ low]; exact stored.2 i

end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- A full actual signing iteration, including the loop's advance and branch. -/
theorem sign_layer (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level index : Nat)
    (current : Reference.Digest) (pc : s.pc = 0x1220) (bound : level < 160) (small : index < 2^192)
    (data : LoopData s secretKey level index current) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles
      (if level = 0 then 5 else 739) (if level = 0 then 5 else 761) final ∧
      instructions ≤ (if level = 0 then 588 else 100454) ∧ cycles ≤ (if level = 0 then 623 else 105803) ∧
      final.pc = (if level+1=160 then 0x12f8 else 0x1220) ∧
      LoopData final secretKey (level+1) (index/2) (Reference.treeRoot hash secretKey level (index/2)) ∧
      LayerStored final (0x20060+layerOffset level) level
        (Reference.signLayer hash secretKey level (index/2) (index%2==1) current) ∧
      (∀ address : Nat, address<0x80000 → address%8=0 →
        OutsideLayer (0x20060+layerOffset level) level (BitVec.ofNat 64 address) →
        final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) := by
  obtain ⟨ready,pre,readyPC,readyRA,readySP,context,ptr,mode,selector,digits,preFrame⟩ :=
    sign_layer_prepare hash s secretKey level index current pc bound small data
  have valid := sign_pointer_valid level bound
  obtain ⟨done,n,c,body,nb,cb,donePC,doneSP,root,stored,frame⟩ :=
    sign_tree hash ready secretKey (0x20060+layerOffset level) level (index/2) current (index%2==1)
      readyPC readySP bound valid context ptr (by rw [mode]; decide) selector digits
  have atAdvance : done.pc = 0x12ac := by rw [donePC,readyRA]; decide
  have keep (a : Word) (region : (0x80400≤a.toNat ∧ a.toNat<0x80428) ∨ (0x80440≤a.toNat ∧ a.toNat<0x80450)) :
      done.getMem a = ready.getMem a :=
    frame a (outsideTreeWork_metadata a region) (outsideLayer_high _ _ valid a (by omega))
  have counter : done.getMem 0x80400 = BitVec.ofNat 64 level := (keep _ (by decide)).trans context.levelEq
  have pointer : done.getMem 0x80448 = BitVec.ofNat 64 (0x20060+layerOffset level) := (keep _ (by decide)).trans ptr
  have advance := advance_block sign 0x12ac sign_advance_code done atAdvance
  have after := advanceState_layer done 0x20060 level bound counter pointer
  have zero : done.getMem 0x80400 = 0 ↔ level = 0 := by rw [counter]; exact level_word_zero level bound
  have nextPC : (advanceState done).pc = (if level+1=160 then 0x12f8 else 0x1220) := by
    simpa using advanceState_layer_pc done 0x12ac level atAdvance bound counter
  have total := pre.trans (body.trans advance.trace)
  simp only [zero,Nat.zero_add,Nat.add_zero] at total
  refine ⟨advanceState done,_,_,total,?_,?_,nextPC,?_,?_,?_⟩
  · by_cases h : level=0
    · simp only [h, if_true] at nb ⊢; omega
    · by_cases flip : Reference.needsFlip current <;>
        simp only [h, flip, if_true, if_false] at nb ⊢ <;> omega
  · by_cases h : level=0
    · simp only [h, if_true] at cb ⊢; omega
    · by_cases flip : Reference.needsFlip current <;>
        simp only [h, flip, if_true, if_false] at cb ⊢ <;> omega
  · constructor
    · rw [advanceState_sp,doneSP,readySP]
    · exact after.1
    · intro i
      rw [advanceState_mem,if_neg (by fin_cases i <;> decide),if_neg (by fin_cases i <;> decide),
        keep _ (by fin_cases i <;> decide)]
      exact context.indexEq i
    · intro i
      have low : (wordAddress 0x20 i.val).toNat < 0x80000 := by fin_cases i <;> decide
      have outside : OutsideLayer (0x20060+layerOffset level) level (wordAddress 0x20 i.val) := by
        left; simp only [wordAddress,BitVec.toNat_ofNat]; have := i.isLt; omega
      rw [advance_low_frame done _ low,frame _ (outsideTreeWork_low _ low) outside]
      exact context.secretKeyEq i
    · rw [advanceState_mem,if_neg (by decide),if_neg (by decide),keep _ (by decide)]; exact mode
    · exact after.2
    · intro i
      rw [advanceState_mem,if_neg (by fin_cases i <;> decide),if_neg (by fin_cases i <;> decide)]
      exact root i
  · exact stored.frame done (advanceState done) _ _ _ valid (advance_low_frame done)
  · intro address low aligned outside
    have lowWord : (BitVec.ofNat 64 address).toNat < 0x80000 := by
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show address<2^64 by omega)] using low
    rw [advance_low_frame done _ lowWord,frame _ (outsideTreeWork_low _ lowWord) outside,preFrame address low aligned]

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_layer
end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

def LayersStored (s : MachineState) : Nat → List Reference.LayerSignature → Prop
  | _, [] => True
  | level, signature :: rest => LayerStored s (0x20060+layerOffset level) level signature ∧ LayersStored s (level+1) rest

theorem layerOffset_mono (a b : Nat) (le : a ≤ b) : layerOffset a ≤ layerOffset b := by
  unfold layerOffset
  split <;> split <;> omega

theorem layer_value_before_next (level : Nat) (_bound : level<160) (chain : Reference.Chain)
    (usable : level=0 → chain.val=0) (i : Fin 2) :
    0x20060+layerOffset level+16*chain.val+8*i.val < 0x20060+layerOffset (level+1) := by
  rw [layerOffset_succ]
  have cb := chain.isLt; have ib := i.isLt
  split <;> rename_i h <;> simp_all <;> omega

theorem LayerStored.prefix_frame (s final : MachineState) (level : Nat) (signature : Reference.LayerSignature)
    (bound : level<160) (stored : LayerStored s (0x20060+layerOffset level) level signature)
    (frame : ∀ address : Nat, address<0x80000 → address%8=0 → address<0x20060+layerOffset (level+1) →
      final.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address)) :
    LayerStored final (0x20060+layerOffset level) level signature := by
  have valid := sign_pointer_valid level bound
  have aligned := valid.2.2
  have upper := valid.2.1
  unfold LayerStored at *
  split at stored <;> rename_i h
  · rw [if_pos h]
    constructor
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16*(0:Reference.Chain).val+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (layer_value_before_next level bound 0 (by simp) i)]
      exact stored.1 i
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (by rw [layerOffset_succ]; rw [if_pos h]; omega)]
      exact stored.2 i
  · rw [if_neg h]
    constructor
    · intro chain i
      have cb := chain.isLt; have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+16*chain.val+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (layer_value_before_next level bound chain (by simp [h]) i)]
      exact stored.1 chain i
    · intro i
      have ib := i.isLt
      change final.getMem (BitVec.ofNat 64 (0x20060+layerOffset level+736+8*i.val)) = _
      rw [frame _ (by omega) (by omega) (by rw [layerOffset_succ]; rw [if_neg h]; omega)]
      exact stored.2 i

end SigGolfCandidate.Hypertree.Signing
