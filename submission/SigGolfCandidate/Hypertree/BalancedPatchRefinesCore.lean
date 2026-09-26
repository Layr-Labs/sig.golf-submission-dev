import SigGolfCandidate.Hypertree.BalancedPatchBodySemantics
import SigGolfCandidate.Hypertree.BalancedPatchWords
import SigGolfCandidate.Hypertree.BalancedPatchExit
import SigGolfCandidate.Hypertree.BalancedPatchControl
import SigGolfCandidate.Hypertree.BalancedPatchSetup
import SigGolfCandidate.Hypertree.BalancedPatchRest
import SigGolfCandidate.Hypertree.BalancedPatchFlip

/-! Inlined from SigGolfCandidate.Hypertree.BalancedPatchRun; its only importer was SigGolfCandidate.Hypertree.BalancedPatchRefinesCore. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion

theorem pc_no_flip (s : MachineState) (forward : BitVec 21) (c : Nat)
    (bound : c ≤ 301) (sum : (entryState s forward).getReg .x12 = BitVec.ofNat 64 c)
    (noFlip : c < 151) :
    (testState (entryState s forward)).pc = (entryState s forward).pc + 140 := by
  have hp := test_pc (entryState s forward) c bound sum
  rw [if_pos noFlip] at hp
  exact hp

theorem entry_test_skip_pc (s : MachineState) (entry start : Word)
    (forward : BitVec 21) (pc : s.pc = entry)
    (offset : entry + signExtend21 forward = start)
    (c : Nat) (bound : c ≤ 301)
    (sum : s.getReg .x12 = BitVec.ofNat 64 c)
    (noFlip : c < 151) :
    (testState (entryState s forward)).pc = start + 140 := by
  have input : (entryState s forward).getReg .x12 = BitVec.ofNat 64 c :=
    (entry_reg s forward .x12).trans sum
  exact (pc_no_flip s forward c bound input noFlip).trans
    (congrArg (· + 140) (entry_pc s entry start forward pc offset))
end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def noFlipResult (s : MachineState) (forward back : BitVec 21) : MachineState :=
  skipState (testState (entryState s forward)) back

theorem noFlip_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (c : Nat) (bound : c ≤ 301) (sum : s.getReg .x12 = BitVec.ofNat 64 c)
    (noFlip : c < 151) :
    OrdinarySteps image s 6 (noFlipResult s forward back) ∧
    (noFlipResult s forward back).pc = entry+4 ∧
    (noFlipResult s forward back).getReg .x12 = BitVec.ofNat 64 c ∧
    (noFlipResult s forward back).getReg .x13 = BitVec.ofNat 64 c &&& 7 ∧
    (∀ a, (noFlipResult s forward back).getByte a = s.getByte a) ∧
    (noFlipResult s forward back).getReg .x10 = s.getReg .x10 ∧
    (noFlipResult s forward back).getReg .x1 = s.getReg .x1 ∧
    (noFlipResult s forward back).getReg .x2 = s.getReg .x2 := by
  have b1 := entry_block image entry start forward back code s pc
  have b2 := test_block image start
    (patch_test_code image entry start forward back code) (entryState s forward)
    (entry_pc s entry start forward pc forwardPC)
  have b3 := skip_block image entry start forward back code
    (testState (entryState s forward))
    (entry_test_skip_pc s entry start forward pc forwardPC c bound sum noFlip)
  refine ⟨Keygen.ordinary_trans image s _ _ 4 2
    (Keygen.ordinary_trans image s _ _ 1 3 b1 b2) b3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact skip_pc _ entry start back
      (entry_test_skip_pc s entry start forward pc forwardPC c bound sum noFlip) backPC
  · rw [noFlipResult,skip_x12,test_reg _ .x12 (by decide),entry_reg,sum]
  · rw [noFlipResult,skip_x13,test_reg _ .x12 (by decide),entry_reg,sum]
    rfl
  · intro a
    simp only [MachineState.getByte,noFlipResult,skip_mem,test_mem,entry_mem]
  · simp [noFlipResult,skipState,execInstrBr,
      MachineState.getReg_setReg_ne,test_reg _ .x10 (by decide),entry_reg]
  · rw [noFlipResult,skip_ra,test_reg _ .x1 (by decide),entry_reg]
  · rw [noFlipResult,skip_sp,test_reg _ .x2 (by decide),entry_reg]

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

/-- The flipped bytes encode the balanced payload digit on the low-sum branch. -/
theorem flipBody_payload (s : MachineState) (message : Reference.Digest)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (flip : Reference.needsFlip message) :
    ∀ i : Fin 43,
      (flipBody s).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i) := by
  have bound (i : Fin 43) : Reference.messageDigit message i < 8 := by
    unfold Reference.messageDigit
    exact Nat.mod_lt _ (by decide)
  have rawBound : ∀ i : Fin 43,
      (s.getByte (BitVec.ofNat 64 (0x80600+i.val))).toNat ≤ 7 := by
    intro i
    rw [rawDigits i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bound i; omega :
      Reference.messageDigit message i < 2^8)]
    have := bound i
    omega
  intro i
  have changed := flipBody_byte s i base mask rawBound
  rw [rawDigits i, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := bound i; omega : Reference.messageDigit message i < 2^8)] at changed
  simpa only [Reference.payloadDigit, if_pos flip] using changed

/-- The low-sum branch is the only path that changes raw message digits. -/
theorem rawDigits_payload_no_flip (s : MachineState) (message : Reference.Digest)
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (noFlip : ¬ Reference.needsFlip message) :
    ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i) := by
  intro i
  simpa only [Reference.payloadDigit, if_neg noFlip] using rawDigits i

#print axioms flipBody_payload
#print axioms rawDigits_payload_no_flip
end SigGolfCandidate.Hypertree.Signing



namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

theorem wordPass_ra (s : MachineState) :
    (wordPass s).getReg .x1 = s.getReg .x1 := by
  simp [wordPass, flipChunk, execInstrBr, MachineState.getReg_setReg_ne]

theorem setup_x10 (s : MachineState) :
    (setupState s).getReg .x10 = s.getReg .x10 := by
  simp [setupState, execInstrBr, MachineState.getReg_setReg_ne]

theorem finish_x10 (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x10 = s.getReg .x10 := by
  simp [finishState, execInstrBr, MachineState.getReg_setReg_ne]

#print axioms wordPass_ra
#print axioms setup_x10
#print axioms finish_x10
end SigGolfCandidate.Hypertree.Signing


namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem flipResult_low (s : MachineState) (forward back : BitVec 21) :
    (flipResult s forward back).getReg .x13 =
      (flipResult s forward back).getReg .x12 &&& 7 := by
  change (finishState (flipBody (setupState (testState (entryState s forward)))) back).getReg .x13 =
    (finishState (flipBody (setupState (testState (entryState s forward)))) back).getReg .x12 &&& 7
  rw [finish_x13,finish_x12]
  rfl

theorem flipResult_x10 (s : MachineState) (forward back : BitVec 21) :
    (flipResult s forward back).getReg .x10 = s.getReg .x10 := by
  rw [flipResult,finish_x10,(tailPass_regs _).2.2.2.1,
    (wordPass_regs _).2.2.2.1,setup_x10,test_reg _ .x10 (by decide),entry_reg]

theorem flipResult_ra (s : MachineState) (forward back : BitVec 21) :
    (flipResult s forward back).getReg .x1 = s.getReg .x1 := by
  rw [flipResult,finish_ra,tailPass_ra,wordPass_ra,setup_ra,
    test_reg _ .x1 (by decide),entry_reg]

theorem flipResult_sp (s : MachineState) (forward back : BitVec 21) :
    (flipResult s forward back).getReg .x2 = s.getReg .x2 := by
  rw [flipResult,finish_sp,(tailPass_regs _).2.2.2.2,
    (wordPass_regs _).2.2.2.2,setup_sp,test_reg _ .x2 (by decide),entry_reg]

theorem flipResult_byte (s : MachineState) (forward back : BitVec 21)
    (message : Reference.Digest)
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (flip : Reference.needsFlip message) (i : Fin 43) :
    (flipResult s forward back).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
      BitVec.ofNat 8 (Reference.payloadDigit message i) := by
  let pre := setupState (testState (entryState s forward))
  have rawPre : ∀ j : Fin 43,
      pre.getByte (BitVec.ofNat 64 (0x80600+j.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message j) := by
    intro j
    have same : pre.getByte (BitVec.ofNat 64 (0x80600+j.val)) =
        s.getByte (BitVec.ofNat 64 (0x80600+j.val)) := by
      simp only [MachineState.getByte,pre,setup_mem,test_mem,entry_mem]
    rw [same]
    exact rawDigits j
  have payload := flipBody_payload pre message (setup_x15 _) (setup_x16 _) rawPre flip i
  change (finishState (flipBody pre) back).getByte _ = _
  simpa only [MachineState.getByte,finish_mem] using payload

theorem flipResult_frame (s : MachineState) (forward back : BitVec 21)
    (a : Word)
    (outside : ∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val)) :
    (flipResult s forward back).getByte a = s.getByte a := by
  let pre := setupState (testState (entryState s forward))
  have frame := flipBody_frame pre a (setup_x15 _) outside
  change (finishState (flipBody pre) back).getByte a = _
  rw [show (finishState (flipBody pre) back).getByte a =
      (flipBody pre).getByte a by simp only [MachineState.getByte,finish_mem], frame]
  simp only [MachineState.getByte,pre,setup_mem,test_mem,entry_mem]

end SigGolfCandidate.Hypertree.Signing
