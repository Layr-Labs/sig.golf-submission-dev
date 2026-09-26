import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoop67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0x500)
  let s := execInstrBr s (.LUI .x11 0x80)
  let s := execInstrBr s (.ADDI .x11 .x11 0x600)
  let s := execInstrBr s (.ADDI .x6 .x10 0)
  let s := execInstrBr s (.ADDI .x14 .x0 0)
  let s := execInstrBr s (.ADDI .x18 .x0 16)
  execInstrBr s (.ADDI .x17 .x2 0)

private theorem word659 : GroupedBalancedVerifyImage67Fast2Byte.code[659]? =
    some 0x00080537 := by decide
private theorem word660 : GroupedBalancedVerifyImage67Fast2Byte.code[660]? =
    some 0x50050513 := by decide
private theorem word661 : GroupedBalancedVerifyImage67Fast2Byte.code[661]? =
    some 0x000805b7 := by decide
private theorem word662 : GroupedBalancedVerifyImage67Fast2Byte.code[662]? =
    some 0x60058593 := by decide
private theorem word663 : GroupedBalancedVerifyImage67Fast2Byte.code[663]? =
    some 0x00050313 := by decide
private theorem word664 : GroupedBalancedVerifyImage67Fast2Byte.code[664]? =
    some 0x00000713 := by decide
private theorem word665 : GroupedBalancedVerifyImage67Fast2Byte.code[665]? =
    some 0x01000913 := by decide
private theorem word666 : GroupedBalancedVerifyImage67Fast2Byte.code[666]? =
    some 0x00010893 := by decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1a4c) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 8 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0x500)
  let s3 := execInstrBr s2 (.LUI .x11 0x80)
  let s4 := execInstrBr s3 (.ADDI .x11 .x11 0x600)
  let s5 := execInstrBr s4 (.ADDI .x6 .x10 0)
  let s6 := execInstrBr s5 (.ADDI .x14 .x0 0)
  let s7 := execInstrBr s6 (.ADDI .x18 .x0 16)
  let s8 := execInstrBr s7 (.ADDI .x17 .x2 0)
  change OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 8 s8
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 7
  · simp [fetch, pc, GroupedBalancedVerifyImage67Fast2Byte.image, word659]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0x500)) 6
  · have hp : s1.pc = 0x1a50 := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word660]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x11 0x80)) 5
  · have hp : s2.pc = 0x1a54 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word661]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x11 .x11 0x600)) 4
  · have hp : s3.pc = 0x1a58 := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word662]; rfl
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x10 0)) 3
  · have hp : s4.pc = 0x1a5c := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word663]; rfl
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x14 .x0 0)) 2
  · have hp : s5.pc = 0x1a60 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word664]; rfl
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x18 .x0 16)) 1
  · have hp : s6.pc = 0x1a64 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word665]; rfl
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x17 .x2 0)) 0
  · have hp : s7.pc = 0x1a68 := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word666]; rfl
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x1a4c)
    (stack : s.getReg .x2 = 0xfff700) :
    (setupState s).pc = 0x1a6c ∧
    (setupState s).getReg .x10 = 0x80500 ∧
    (setupState s).getReg .x11 = 0x80600 ∧
    (setupState s).getReg .x6 = 0x80500 ∧
    (setupState s).getReg .x14 = 0 ∧
    (setupState s).getReg .x18 = 16 ∧
    (setupState s).getReg .x17 = 0xfff700 ∧
    (setupState s).getReg .x2 = 0xfff700 := by
  simp [setupState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12, pc, stack]

theorem setup_byte (s : MachineState) (a : Word) :
    (setupState s).getByte a = s.getByte a := by
  simp [setupState, execInstrBr, MachineState.getByte,
    MachineState.getMem_setReg, MachineState.getMem_setPC]

#print axioms setup_steps
#print axioms setup_fields
#print axioms setup_byte

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67

def fullDecoderState (s : MachineState) (message : BitVec 128) : MachineState :=
  postSumState (sumLoop (setupState s) 16) message

private theorem sumBody_x10 (s : MachineState) :
    (sumBody s).getReg .x10 = s.getReg .x10 := by
  simp [sumBody, execInstrBr, MachineState.getReg_setReg_ne]
private theorem sumBody_x11 (s : MachineState) :
    (sumBody s).getReg .x11 = s.getReg .x11 := by
  simp [sumBody, execInstrBr, MachineState.getReg_setReg_ne]
private theorem sumBody_x2 (s : MachineState) :
    (sumBody s).getReg .x2 = s.getReg .x2 := by
  simp [sumBody, execInstrBr, MachineState.getReg_setReg_ne]

theorem sumLoop_x10 (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x10 = s.getReg .x10 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_x10] using ih
theorem sumLoop_x11 (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x11 = s.getReg .x11 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_x11] using ih
theorem sumLoop_x2 (s : MachineState) (n : Nat) :
    (sumLoop s n).getReg .x2 = s.getReg .x2 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_x2] using ih

#print axioms sumLoop_x2

theorem fullDecoder_steps (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a4c)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (hsum : ∀ entry : Fin 256,
      s.getByte (BitVec.ofNat 64 (0xfff700+entry.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val)) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s
      (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6)
      (fullDecoderState s message) := by
  let p := setupState s
  let q := sumLoop p 16
  have hs := setup_fields s pc stack
  rcases hs with ⟨hpc,hx10,hx11,hx6,hx14,hx18,hx17,hx2⟩
  have hmsg_p : ∀ j : Fin 16,
      p.getByte (p.getReg .x6 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8 := by
    intro j
    change (setupState s).getByte _ = _
    rw [hx6, setup_byte]
    have ha : (0x80500 : Word) + BitVec.ofNat 64 j.val =
        BitVec.ofNat 64 (0x80500+j.val) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [ha]
    exact hmsg j
  have hsum_p : ∀ entry : Fin 256,
      p.getByte (p.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val) := by
    intro entry
    change (setupState s).getByte _ = _
    rw [hx17, setup_byte]
    have ha : (0xfff700 : Word) + BitVec.ofNat 64 entry.val =
        BitVec.ofNat 64 (0xfff700+entry.val) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [ha]
    exact hsum entry
  have hsumloop := sumLoop_interface_fast p message hpc hx18 hx6 hx17 hx14
    hmsg_p hsum_p
  rcases hsumloop with ⟨hsl,hqpc,hqsum⟩
  have hq2 : q.getReg .x2 = 0xfff700 := by
    rw [sumLoop_x2, hx2]
  have hq10 : q.getReg .x10 = 0x80500 := by
    rw [sumLoop_x10, hx10]
  have hq11 : q.getReg .x11 = 0x80600 := by
    rw [sumLoop_x11, hx11]
  have hpost := postSum_steps q message hqpc hqsum hq2 hq10 hq11
  have hsetup := setup_steps s pc
  have htotal := steps_comp (steps_comp hsetup hsl) hpost
  simpa only [fullDecoderState, p, q, Nat.add_assoc] using htotal

#print axioms fullDecoder_steps

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67
