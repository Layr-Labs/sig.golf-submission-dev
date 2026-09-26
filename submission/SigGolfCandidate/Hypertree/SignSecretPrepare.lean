import SigGolfCandidate.Hypertree.SignChainCapture
import SigGolfCandidate.Hypertree.SignCaptureFrame
import SigGolfCandidate.Hypertree.KeygenSecretExecution
import SigGolfCandidate.Hypertree.KeygenLeafExecution
import SigGolfCandidate.Hypertree.KeygenNodeExecution
import SigGolfCandidate.Hypertree.KeygenEndpoint
import SigGolfCandidate.Hypertree.KeygenStepZero

/-! Inlined from SigGolfCandidate.Hypertree.SignChainUnselected; its only importer was SigGolfCandidate.Hypertree.SignSecretPrepare. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

theorem capture_unselected_mem (s : MachineState)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) (a : Word) :
    (captureUpperState s).getMem a = s.getMem a := by
  rw [captureUpper_mem]
  simp only [unselected, false_and, and_false, if_false]

/-- The signer executes every capture and HASH in a remaining chain fragment. The resource
bound allows the longest capture branch at every step; the HASH count is exact. -/
theorem sign_chain_unselected_loop (hash : Hash) (s : MachineState) (pointer level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1698) (length : start + remaining = 7)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain start value)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles remaining remaining final ∧
      instructions ≤ 131 * remaining + 40 ∧ cycles ≤ 138 * remaining + 40 ∧
      final.pc = 0x1874 ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s start value with
  | zero =>
    have startEq : start = 7 := by omega
    subst start
    have target := capture_target s pointer chain valid ptr data.chainEq
    obtain ⟨safe, safeNext⟩ := capture_access pointer chain valid
    have cap := captureUpper_block sign 0x1698 sign_upper_capture_code s pc
      (capture_digit_access s chain data.chainEq)
      (by rw [target]; exact safe)
      (by rw [target, capture_target_next]; exact safeNext)
    have capPC : (captureUpperState s).pc = 0x1724 := by rw [captureUpper_pc, pc]; rfl
    have capData := captureUpper_chainData s pointer level tree 7 side chain value valid ptr data
    have done := check_block sign 0x1724 sign_chain_check _ capPC
    refine ⟨check (captureUpperState s), captureUpperSteps s + 5, captureUpperSteps s + 5,
      cap.trace.trans done.trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := captureUpper_steps_le s; omega
    · have := captureUpper_steps_le s; omega
    · rw [check_pc, capPC, capData.stepEq]; rfl
    · simpa only [walk] using capData.check
    · exact (check_stack _).1.trans (captureUpper_ra s)
    · exact (check_stack _).2.trans (captureUpper_sp s)
    · intro a _
      rw [check_mem]
      exact capture_unselected_mem s unselected a
  | succ remaining ih =>
    have target := capture_target s pointer chain valid ptr data.chainEq
    obtain ⟨safe, safeNext⟩ := capture_access pointer chain valid
    have cap := captureUpper_block sign 0x1698 sign_upper_capture_code s pc
      (capture_digit_access s chain data.chainEq)
      (by rw [target]; exact safe)
      (by rw [target, capture_target_next]; exact safeNext)
    have capPC : (captureUpperState s).pc = 0x1724 := by rw [captureUpper_pc, pc]; rfl
    have capData := captureUpper_chainData s pointer level tree start side chain value valid ptr data
    obtain ⟨next, core, nextPC, nextData, nextRA, nextSP, nextFrame⟩ := chain_core_step hash
      (captureUpperState s) level tree start side chain value capPC (by omega) capData
    have nextPtr : next.getMem 0x80448 = BitVec.ofNat 64 pointer := by
      rw [nextFrame _ (by unfold OutsideChainWork; decide), captureUpper_high_frame s pointer chain valid ptr data.chainEq _ (by decide)]
      exact ptr
    have nextUnselected : next.getMem 0x80428 ≠ next.getMem 0x80420 := by
      rw [nextFrame _ (by unfold OutsideChainWork; decide), nextFrame _ (by unfold OutsideChainWork; decide),
        capture_unselected_mem s unselected, capture_unselected_mem s unselected]
      exact unselected
    obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData,
      finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC (by omega) nextPtr nextData nextUnselected
    refine ⟨final, captureUpperSteps s + 96 + steps, captureUpperSteps s + 103 + cycles,
      ?_, ?_, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert (cap.trace.trans core).trans tail using 1 <;> omega
    · have := captureUpper_steps_le s; omega
    · have := captureUpper_steps_le s; omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (captureUpper_ra s))
    · exact finalSP.trans (nextSP.trans (captureUpper_sp s))
    · intro a workOutside
      rw [finalFrame a workOutside, nextFrame a workOutside]
      exact capture_unselected_mem s unselected a

/-- The other leaf computes the same endpoint while preserving every signature word. -/
theorem sign_chain_unselected_endpoint (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1698)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain 0 (Reference.secret hash secretKey level tree side chain))
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 7 7 final ∧
      instructions ≤ 957 ∧ cycles ≤ 1006 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) :=
  sign_chain_unselected_loop hash s pointer level tree 0 7 side chain _ pc (by decide) valid ptr data unselected

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv Keygen
set_option maxRecDepth 4096

theorem sign_upper_secret_code : KeygenSecret.Code sign 0x1584 := by decide
theorem sign_bottom_secret_code : KeygenSecret.Code sign 0x19dc := by decide
theorem sign_endpoint_code : KeygenEndpoint.Code sign 0x1874 (-832) := by decide
theorem sign_leaf_compress_code : KeygenLeaf.Code sign 0x18c8 := by decide
theorem sign_leaf_enter_code : EnterCode sign 0x154c := by decide
theorem sign_leaf_return_code : ReturnCode sign 0x19d0 := by decide
theorem sign_bottom_return_code : ReturnCode sign 0x1c64 := by decide
theorem sign_tree_enter_code : EnterCode sign 0x13c8 := by decide
theorem sign_node_body_code : KeygenNode.BodyCode sign 0x1460 := by decide
theorem sign_node_return_code : ReturnCode sign 0x1540 := by decide

end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Metadata and secret key needed at the start of each signer upper-leaf chain. -/
structure LeafData (s : MachineState) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Nat) : Prop where
  levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level
  leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side)
  chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain
  indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) = (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  secretKeyEq : ∀ i : Fin 4, s.getMem (wordAddress 0x20 i.val) = secretKey.extractLsb' (64*i.val) 64

/-- Secret derivation and actual STEP reset initialize the complete signer chain loop. -/
theorem sign_secret_prepare (hash : Hash) (s : MachineState) (secretKey : SecretKey) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (data : LeafData s secretKey level tree side chain.val) :
    ∃ final, Trace hash sign s 93 100 1 1 final ∧ final.pc = 0x1698 ∧
      ChainData final level tree side chain 0 (Reference.secret hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨secret, pre, secretPC, secretWords, ra, sp, frame⟩ := KeygenSecret.compute sign hash 0x1584 sign_upper_secret_code
    s pc level tree side chain secretKey data.levelEq data.leafEq data.chainEq data.indexEq data.secretKeyEq
  have reset := KeygenStepZero.block sign 0x1688 KeygenStepZero.sign_code secret secretPC
  have keep (a : Word) (outside : OutsideChainWork a) : (KeygenStepZero.state secret).getMem a = s.getMem a := by
    rw [KeygenStepZero.mem, if_neg outside.2.2.2, frame a outside.1 outside.2.1 outside.2.2.1]
  refine ⟨KeygenStepZero.state secret, pre.trans reset.trace, ?_, ?_,
    (KeygenStepZero.stack secret).1.trans ra, (KeygenStepZero.stack secret).2.trans sp, keep⟩
  · rw [KeygenStepZero.pc, secretPC]; rfl
  · constructor
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.levelEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.leafEq
    · rw [keep _ (by unfold OutsideChainWork; decide)]; exact data.chainEq
    · rw [KeygenStepZero.mem, if_pos rfl]; rfl
    · intro i
      rw [keep _ (by fin_cases i <;> unfold OutsideChainWork <;> decide)]
      exact data.indexEq i
    · intro i
      rw [KeygenStepZero.mem, if_neg (by fin_cases i <;> decide)]
      exact secretWords i

/-- A full selected signer chain derives its secret, computes the endpoint, and writes the
reference signature checkpoint, using exactly eight compression calls. -/
theorem sign_selected_chain (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (message : Reference.Digest)
    (pc : s.pc = 0x1584) (upper : level ≠ 0) (valid : CapturePointerValid pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (settings : CaptureSettings s pointer chain (Reference.digit message chain)) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
      instructions ≤ 1050 ∧ cycles ≤ 1106 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      CapturedValue final pointer chain ((Reference.signLayer hash secretKey level tree side message).values chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, readyPC, readyData, readyRA, readySP, readyFrame⟩ :=
    sign_secret_prepare hash s secretKey level tree side chain pc data
  have readySettings := settings.frame s ready pointer chain _ valid (fun a outside _ => readyFrame a outside)
  obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData, captured,
    finalRA, finalSP, finalFrame⟩ := sign_chain_captured_endpoint hash ready secretKey pointer level tree side chain message
      readyPC upper valid readyData readySettings
  refine ⟨final, 93 + steps, 100 + cycles, pre.trans tail, by omega, by omega,
    finalPC, finalData, captured, finalRA.trans readyRA, finalSP.trans readySP, ?_⟩
  intro a outside captureOutside
  rw [finalFrame a outside captureOutside, readyFrame a outside]

/-- The other leaf's full chain also costs exactly eight compressions and preserves the signature. -/
theorem sign_unselected_chain (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1584)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : LeafData s secretKey level tree side chain.val)
    (unselected : s.getMem 0x80428 ≠ s.getMem 0x80420) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 8 8 final ∧
      instructions ≤ 1050 ∧ cycles ≤ 1106 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, readyPC, readyData, readyRA, readySP, readyFrame⟩ :=
    sign_secret_prepare hash s secretKey level tree side chain pc data
  have readyPtr : ready.getMem 0x80448 = BitVec.ofNat 64 pointer := by
    rw [readyFrame _ (by unfold OutsideChainWork; decide)]; exact ptr
  have readyUnselected : ready.getMem 0x80428 ≠ ready.getMem 0x80420 := by
    rw [readyFrame _ (by unfold OutsideChainWork; decide), readyFrame _ (by unfold OutsideChainWork; decide)]
    exact unselected
  obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData,
    finalRA, finalSP, finalFrame⟩ := sign_chain_unselected_endpoint hash ready secretKey pointer level tree side chain
      readyPC valid readyPtr readyData readyUnselected
  refine ⟨final, 93 + steps, 100 + cycles, pre.trans tail, by omega, by omega,
    finalPC, finalData, finalRA.trans readyRA, finalSP.trans readySP, ?_⟩
  intro a outside
  rw [finalFrame a outside, readyFrame a outside]

end SigGolfCandidate.Hypertree.Signing
