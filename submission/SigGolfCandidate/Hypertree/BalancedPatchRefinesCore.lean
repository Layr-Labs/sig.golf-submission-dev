import SigGolfCandidate.Hypertree.BalancedPatchRun
import SigGolfCandidate.Hypertree.BalancedPatchFlip
import SigGolfCandidate.Hypertree.BalancedPatchFrameRegs
import SigGolfCandidate.Hypertree.BalancedPatchPayload

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
