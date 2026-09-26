import SigGolfCandidate.Hypertree.SignCaptureFrame

/-! Inlined from SigGolfCandidate.Hypertree.SignChainLoop; its only importer was SigGolfCandidate.Hypertree.SignCaptureRefine. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

/-- The signer executes every capture and HASH in a remaining chain fragment. The resource
bound allows the longest capture branch at every step; the HASH count is exact. -/
theorem sign_chain_loop (hash : Hash) (s : MachineState) (pointer level tree start remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1698) (length : start + remaining = 7)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain start value) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles remaining remaining final ∧
      instructions ≤ 131 * remaining + 40 ∧ cycles ≤ 138 * remaining + 40 ∧
      final.pc = 0x1874 ∧
      ChainData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) start remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) := by
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
    · intro a _ outside
      rw [check_mem]
      exact captureUpper_frame s pointer chain valid ptr data.chainEq a outside
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
    obtain ⟨final, steps, cycles, tail, stepsBound, cyclesBound, finalPC, finalData,
      finalRA, finalSP, finalFrame⟩ := ih next (start+1)
      (Reference.chainHash hash level tree side chain start value) nextPC (by omega) nextPtr nextData
    refine ⟨final, captureUpperSteps s + 96 + steps, captureUpperSteps s + 103 + cycles,
      ?_, ?_, ?_, finalPC, ?_, ?_, ?_, ?_⟩
    · convert (cap.trace.trans core).trans tail using 1 <;> omega
    · have := captureUpper_steps_le s; omega
    · have := captureUpper_steps_le s; omega
    · simpa only [walk] using finalData
    · exact finalRA.trans (nextRA.trans (captureUpper_ra s))
    · exact finalSP.trans (nextSP.trans (captureUpper_sp s))
    · intro a workOutside captureOutside
      rw [finalFrame a workOutside captureOutside, nextFrame a workOutside]
      exact captureUpper_frame s pointer chain valid ptr data.chainEq a captureOutside

/-- A complete signer chain computes exactly the reference endpoint, including the final
step-seven capture, with seven compression calls and a uniform cycle bound. -/
theorem sign_chain_endpoint (hash : Hash) (s : MachineState) (secretKey : SecretKey) (pointer level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (pc : s.pc = 0x1698)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain 0 (Reference.secret hash secretKey level tree side chain)) :
    ∃ final instructions cycles, Trace hash sign s instructions cycles 7 7 final ∧
      instructions ≤ 957 ∧ cycles ≤ 1006 ∧ final.pc = 0x1874 ∧
      ChainData final level tree side chain 7 (Reference.endpoint hash secretKey level tree side chain) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a →
        (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :=
  sign_chain_loop hash s pointer level tree 0 7 side chain _ pc (by decide) valid ptr data

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_chain_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_chain_endpoint

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

structure CaptureSettings (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8) : Prop where
  pointerEq : s.getMem 0x80448 = BitVec.ofNat 64 pointer
  enabled : s.getMem 0x80440 ≠ 0
  selected : s.getMem 0x80428 = s.getMem 0x80420
  digitEq : s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) = BitVec.ofNat 8 digit.val

def CapturedValue (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (value : Reference.Digest) : Prop :=
  ∀ i : Fin 2, s.getMem (wordAddress (pointer + 16 * chain.val) i.val) = value.extractLsb' (64 * i.val) 64

theorem capture_matches_iff (s : MachineState) (pointer step : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (settings : CaptureSettings s pointer chain digit) (bound : step ≤ 7)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (stp : s.getMem 0x80438 = BitVec.ofNat 64 step) :
    CaptureDigitMatches s ↔ step = digit.val := by
  unfold CaptureDigitMatches
  rw [chn, show (0x80600 : Word) + BitVec.ofNat 64 chain.val = BitVec.ofNat 64 (0x80600 + chain.val)
    from (BitVec.ofNat_add _ _).symm, settings.digitEq, stp]
  rw [BitVec.toNat_eq]
  have dbound := digit.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem capture_selected_value (s : MachineState) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (data : ChainData s level tree side chain step value) (bound : step ≤ 7)
    (matching : step = digit.val) : CapturedValue (captureUpperState s) pointer chain value := by
  have test := (capture_matches_iff s pointer step chain digit settings bound data.chainEq data.stepEq).2 matching
  have condition : s.getMem 0x80440 ≠ 0 ∧ s.getMem 0x80428 = s.getMem 0x80420 ∧ CaptureDigitMatches s :=
    ⟨settings.enabled, settings.selected, test⟩
  intro i
  rw [captureUpper_mem, if_pos condition,
    capture_target s pointer chain valid settings.pointerEq data.chainEq]
  have ne : BitVec.ofNat 64 (pointer + 16 * chain.val) ≠ BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 := by
    intro eq
    have : (8 : Word) = 0 := BitVec.add_right_eq_self.mp eq.symm
    contradiction
  fin_cases i
  · change (if BitVec.ofNat 64 (pointer + 16 * chain.val) = BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 then _ else _) = _
    rw [if_neg ne]
    simpa [wordAddress] using data.valueEq 0
  · have address : wordAddress (pointer + 16 * chain.val) 1 = BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 :=
      BitVec.ofNat_add _ _
    rw [address, if_pos rfl]
    exact data.valueEq 1

theorem capture_selected_keep (s : MachineState) (pointer step : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (settings : CaptureSettings s pointer chain digit) (bound : step ≤ 7)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (stp : s.getMem 0x80438 = BitVec.ofNat 64 step) (different : step ≠ digit.val) (a : Word) :
    (captureUpperState s).getMem a = s.getMem a := by
  rw [captureUpper_mem]
  have test : ¬ CaptureDigitMatches s := by
    rw [capture_matches_iff s pointer step chain digit settings bound chn stp]
    exact different
  simp only [test, and_false, if_false]

/-- Settings live outside both the hash workspace and this chain's output pair. -/
theorem CaptureSettings.frame (s final : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (frame : ∀ a, OutsideChainWork a →
      (∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) → final.getMem a = s.getMem a) :
    CaptureSettings final pointer chain digit := by
  have outside (a : Word) (high : 0x80000 ≤ a.toNat) :
      ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val := by
    intro i eq
    have bound := chain.isLt
    have ibound := i.isLt
    rcases valid with ⟨lower, upper, aligned⟩
    have h := congrArg BitVec.toNat eq
    simp only [wordAddress, BitVec.toNat_ofNat] at h
    omega
  have keep (a : Word) (work : OutsideChainWork a) (high : 0x80000 ≤ a.toNat) := frame a work (outside a high)
  constructor
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide)]; exact settings.pointerEq
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide)]; exact settings.enabled
  · rw [keep _ (by unfold OutsideChainWork; decide) (by decide), keep _ (by unfold OutsideChainWork; decide) (by decide)]
    exact settings.selected
  · rw [getByte_word final 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
    rw [keep]
    · rw [← getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega)]
      exact settings.digitEq
    · have bound := chain.isLt
      unfold OutsideChainWork
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals (first | intro j eq | intro eq)
      all_goals have h := congrArg BitVec.toNat eq
      all_goals simp [wordAddress] at h
      all_goals omega
    · have bound := chain.isLt
      simp only [wordAddress, BitVec.toNat_ofNat]
      omega

theorem capture_settings (s : MachineState) (pointer : Nat) (chain : Reference.Chain) (digit : Fin 8)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    CaptureSettings (captureUpperState s) pointer chain digit :=
  settings.frame s (captureUpperState s) pointer chain digit valid
    (fun a _ outside => captureUpper_frame s pointer chain valid settings.pointerEq chn a outside)

theorem capture_output_outside_work (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer) (i : Fin 2) :
    OutsideChainWork (wordAddress (pointer + 16 * chain.val) i.val) := by
  have bound := chain.isLt
  have ibound := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  unfold OutsideChainWork
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals (first | intro j eq | intro eq)
  all_goals have h := congrArg BitVec.toNat eq
  all_goals simp [wordAddress] at h
  all_goals omega

/-- Immediately after capture, a checkpoint at or before this iteration is stored. -/
theorem capture_completed_checkpoint (s : MachineState) (hash : Hash) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8) (value expected : Reference.Digest)
    (valid : CapturePointerValid pointer) (settings : CaptureSettings s pointer chain digit)
    (data : ChainData s level tree side chain step value) (bound : step ≤ 7)
    (future : step ≤ digit.val → expected = walk (Reference.chainHash hash level tree side chain) step (digit.val - step) value)
    (past : digit.val < step → CapturedValue s pointer chain expected)
    (reached : digit.val ≤ step) : CapturedValue (captureUpperState s) pointer chain expected := by
  by_cases eq : step = digit.val
  · have expectedEq : expected = value := by simpa [eq, walk] using future (by omega)
    rw [expectedEq]
    exact capture_selected_value s pointer level tree step side chain digit value valid settings data bound eq
  · have old := past (by omega)
    intro i
    rw [capture_selected_keep s pointer step chain digit settings bound data.chainEq data.stepEq eq]
    exact old i

end SigGolfCandidate.Hypertree.Signing
