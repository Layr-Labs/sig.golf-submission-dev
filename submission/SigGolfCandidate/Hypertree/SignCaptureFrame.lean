import SigGolfCandidate.Hypertree.SignCaptureUpper
import SigGolfCandidate.Hypertree.VerifyChainStep

/-! Inlined from SigGolfCandidate.Hypertree.SignChainStep; its only importer was SigGolfCandidate.Hypertree.SignCaptureFrame. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096

/-- The signer writes only the two-word chain value, so its frame preserves both public slots. -/
def OutsideChainWork (a : Word) : Prop :=
  (∀ i : Fin 8, a ≠ wordAddress 0x80000 i.val) ∧
  (∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val) ∧
  (∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) ∧ a ≠ 0x80438

theorem sign_chain_check : CheckCode sign 0x1724 := by decide
theorem sign_chain_code : KeygenChain.Code sign 0x1738 := by decide
theorem sign_chain_increment : IncrementCode sign 0x1854 (-472) := by decide

/-- One signer chain iteration after its capture block, including its test, actual HASH core and increment. -/
theorem chain_core_step (hash : Hash) (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1724) (bound : step < 7) (data : ChainData s level tree side chain step value) :
    ∃ final, Trace hash sign s 96 103 1 1 final ∧ final.pc = 0x1698 ∧
      ChainData final level tree side chain (step+1) (Reference.chainHash hash level tree side chain step value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideChainWork a → final.getMem a = s.getMem a) := by
  have ne : s.getMem 0x80438 ≠ 7 := by
    rw [data.stepEq]
    intro eq
    have h := congrArg BitVec.toNat eq
    change step % 2^64 = 7 at h
    omega
  have checkedPC : (check s).pc = 0x1738 := by rw [check_pc, pc, if_neg ne]; rfl
  have checked := data.check
  obtain ⟨hashed, core, hashedPC, valueOut, ra, sp, frame⟩ := KeygenChain.compute sign hash 0x1738 sign_chain_code
    (check s) checkedPC level tree step side chain value checked.levelEq checked.leafEq checked.chainEq
    checked.stepEq checked.indexEq checked.valueEq
  have hashedPC' : hashed.pc = 0x1854 := hashedPC
  have tail := increment_block sign 0x1854 (-472) sign_chain_increment hashed hashedPC'
  have keep (a : Word)
      (hi : ∀ i : Fin 6, a ≠ wordAddress 0x80000 i.val)
      (ha : ∀ i : Fin 4, a ≠ wordAddress 0x80300 i.val)
      (hv : ∀ i : Fin 2, a ≠ wordAddress 0x80510 i.val) : hashed.getMem a = s.getMem a := by
    rw [frame a hi ha hv, check_mem]
  have nextLevel : hashed.getMem 0x80400 = s.getMem 0x80400 := keep _ (by decide) (by decide) (by decide)
  have nextLeaf : hashed.getMem 0x80428 = s.getMem 0x80428 := keep _ (by decide) (by decide) (by decide)
  have nextChain : hashed.getMem 0x80430 = s.getMem 0x80430 := keep _ (by decide) (by decide) (by decide)
  have nextStep : hashed.getMem 0x80438 = s.getMem 0x80438 := keep _ (by decide) (by decide) (by decide)
  refine ⟨increment hashed (-472), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((check_block sign 0x1724 sign_chain_check s pc).trace.trans core).trans tail.trace
  · rw [increment_pc, hashedPC']; rfl
  · constructor
    · rw [increment_mem, if_neg (by decide), nextLevel]; exact data.levelEq
    · rw [increment_mem, if_neg (by decide), nextLeaf]; exact data.leafEq
    · rw [increment_mem, if_neg (by decide), nextChain]; exact data.chainEq
    · rw [increment_mem, if_pos rfl, nextStep, data.stepEq, BitVec.ofNat_add]; rfl
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide), keep]
      · exact data.indexEq i
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
      · intro j; fin_cases i <;> fin_cases j <;> decide
    · intro i
      rw [increment_mem, if_neg (by fin_cases i <;> decide)]
      exact valueOut i
  · exact (increment_stack hashed (-472)).1.trans (ra.trans (check_stack s).1)
  · exact (increment_stack hashed (-472)).2.trans (sp.trans (check_stack s).2)
  · intro a outside
    rw [increment_mem, if_neg outside.2.2.2, keep a (fun i => outside.1 ⟨i.val, by omega⟩)
      outside.2.1 outside.2.2.1]


end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen ChainLoopControl Verifying
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def CapturePointerValid (pointer : Nat) : Prop :=
  0x20060 ≤ pointer ∧ pointer + 752 ≤ 0x40000 ∧ pointer % 8 = 0

theorem capture_target (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    s.getMem 0x80448 + (s.getMem 0x80430 <<< 4) = BitVec.ofNat 64 (pointer + 16 * chain.val) := by
  rw [ptr, chn]
  apply BitVec.eq_of_toNat_eq
  have bound := chain.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem capture_target_next (pointer : Nat) (chain : Reference.Chain) :
    BitVec.ofNat 64 (pointer + 16 * chain.val) + 8 =
      BitVec.ofNat 64 (pointer + 16 * chain.val + 8) := (BitVec.ofNat_add _ _).symm

theorem capture_access (pointer : Nat) (chain : Reference.Chain) (valid : CapturePointerValid pointer) :
    accessValid (BitVec.ofNat 64 (pointer + 16 * chain.val)) 8 = true ∧
    accessValid (BitVec.ofNat 64 (pointer + 16 * chain.val + 8)) 8 = true := by
  have bound := chain.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  simp [accessValid, rangeValid, MEMORY_BYTES]
  omega

theorem capture_digit_access (s : MachineState) (chain : Reference.Chain)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val) :
    accessValid (0x80600 + s.getMem 0x80430) 1 = true := by
  rw [chn]
  have bound := chain.isLt
  simp [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_add]
  omega

theorem captureUpper_frame (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (a : Word) (outside : ∀ i : Fin 2, a ≠ wordAddress (pointer + 16 * chain.val) i.val) :
    (captureUpperState s).getMem a = s.getMem a := by
  rw [captureUpper_mem, capture_target s pointer chain valid ptr chn, capture_target_next]
  have zero : a ≠ BitVec.ofNat 64 (pointer + 16 * chain.val) := outside 0
  have one : a ≠ BitVec.ofNat 64 (pointer + 16 * chain.val + 8) := outside 1
  simp only [if_neg zero, if_neg one, ite_self]

theorem captureUpper_high_frame (s : MachineState) (pointer : Nat) (chain : Reference.Chain)
    (valid : CapturePointerValid pointer)
    (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (chn : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (a : Word) (high : 0x80000 ≤ a.toNat) :
    (captureUpperState s).getMem a = s.getMem a := by
  apply captureUpper_frame s pointer chain valid ptr chn a
  intro i eq
  have bound := chain.isLt
  have ibound := i.isLt
  rcases valid with ⟨lower, upper, aligned⟩
  have h := congrArg BitVec.toNat eq
  simp only [wordAddress, BitVec.toNat_ofNat] at h
  omega

theorem captureUpper_ra (s : MachineState) :
    (captureUpperState s).getReg .x1 = s.getReg .x1 := by
  unfold captureUpperState
  split
  · simp [captureModeState, execInstrBr, MachineState.getReg_setReg_ne]
  · split
    · unfold captureUpperTailState
      split <;> simp [captureUpperPrepared, captureWriteState, capturePositionState,
        captureDigitState, capturePointerState, captureSelectorState, captureModeState,
        execInstrBr, MachineState.getReg_setReg_ne]
    · simp [captureSelectorState, captureModeState, execInstrBr, MachineState.getReg_setReg_ne]

theorem captureUpper_chainData (s : MachineState) (pointer level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (valid : CapturePointerValid pointer) (ptr : s.getMem 0x80448 = BitVec.ofNat 64 pointer)
    (data : ChainData s level tree side chain step value) :
    ChainData (captureUpperState s) level tree side chain step value := by
  have keep := captureUpper_high_frame s pointer chain valid ptr data.chainEq
  constructor
  · rw [keep _ (by decide)]; exact data.levelEq
  · rw [keep _ (by decide)]; exact data.leafEq
  · rw [keep _ (by decide)]; exact data.chainEq
  · rw [keep _ (by decide)]; exact data.stepEq
  · intro i; rw [keep _ (by fin_cases i <;> decide)]; exact data.indexEq i
  · intro i; rw [keep _ (by fin_cases i <;> decide)]; exact data.valueEq i

end SigGolfCandidate.Hypertree.Signing
