import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranchSteps67
import SigGolfCandidate.Hypertree.GroupedBalancedChecksum67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTail67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTail67

def tailState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x25 .x0 9)
  let s := execInstrBr s (.REMU .x26 .x23 .x25)
  let s := execInstrBr s (.DIVU .x27 .x23 .x25)
  let s := execInstrBr s (.SB .x11 .x26 1)
  let s := execInstrBr s (.SB .x11 .x27 2)
  execInstrBr s (.JALR .x0 .x1 0)

private theorem word696 : GroupedBalancedVerifyImage67Fast2Byte.code[696]? =
    some 0x00900c93 := by decide
private theorem word697 : GroupedBalancedVerifyImage67Fast2Byte.code[697]? =
    some 0x039bfd33 := by decide
private theorem word698 : GroupedBalancedVerifyImage67Fast2Byte.code[698]? =
    some 0x039bddb3 := by decide
private theorem word699 : GroupedBalancedVerifyImage67Fast2Byte.code[699]? =
    some 0x01a580a3 := by decide
private theorem word700 : GroupedBalancedVerifyImage67Fast2Byte.code[700]? =
    some 0x01b58123 := by decide
private theorem word701 : GroupedBalancedVerifyImage67Fast2Byte.code[701]? =
    some 0x00008067 := by decide

theorem tail_steps (s : MachineState) (pc : s.pc = 0x1ae0)
    (valid1 : accessValid (s.getReg .x11 + 1) 1 = true)
    (valid2 : accessValid (s.getReg .x11 + 2) 1 = true) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 6 (tailState s) := by
  let s1 := execInstrBr s (.ADDI .x25 .x0 9)
  let s2 := execInstrBr s1 (.REMU .x26 .x23 .x25)
  let s3 := execInstrBr s2 (.DIVU .x27 .x23 .x25)
  let s4 := execInstrBr s3 (.SB .x11 .x26 1)
  let s5 := execInstrBr s4 (.SB .x11 .x27 2)
  let s6 := execInstrBr s5 (.JALR .x0 .x1 0)
  change OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s 6 s6
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x25 .x0 9)) 5
  · simp [fetch, pc, GroupedBalancedVerifyImage67Fast2Byte.image, word696]; rfl
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.REMU .x26 .x23 .x25)) 4
  · have hp : s1.pc = 0x1ae4 := by simp [s1, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word697]; rfl
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.DIVU .x27 .x23 .x25)) 3
  · have hp : s2.pc = 0x1ae8 := by simp [s1, s2, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word698]; rfl
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SB .x11 .x26 1)) 2
  · have hp : s3.pc = 0x1aec := by simp [s1, s2, s3, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word699]; rfl
  · change (if accessValid (s3.getReg .x11 + signExtend12 (1 : BitVec 12)) 1 = true
      then some s4 else none) = some s4
    have hptr : s3.getReg .x11 = s.getReg .x11 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_ne]
    rw [hptr, show signExtend12 (1 : BitVec 12) = (1 : Word) by decide, valid1]
    rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SB .x11 .x27 2)) 1
  · have hp : s4.pc = 0x1af0 := by simp [s1, s2, s3, s4, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word700]; rfl
  · change (if accessValid (s4.getReg .x11 + signExtend12 (2 : BitVec 12)) 1 = true
      then some s5 else none) = some s5
    have hptr : s4.getReg .x11 = s.getReg .x11 := by
      simp [s1,s2,s3,s4,execInstrBr,MachineState.getReg_setReg_ne,
        MachineState.setByte]
    rw [hptr, show signExtend12 (2 : BitVec 12) = (2 : Word) by decide, valid2]
    rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.JALR .x0 .x1 0)) 0
  · have hp : s5.pc = 0x1af4 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc]
    simp [fetch, hp, GroupedBalancedVerifyImage67Fast2Byte.image, word701]; rfl
  · rfl
  exact OrdinarySteps.refl _

#print axioms tail_steps

theorem rem9 (q : Nat) (hq : q ≤ 192) :
    rv64_remu (BitVec.ofNat 64 q) 9 = BitVec.ofNat 64 (q % 9) := by
  apply BitVec.eq_of_toNat_eq
  unfold rv64_remu
  split
  · rename_i hz
    simp at hz
  · simp only [BitVec.toNat_umod, BitVec.toNat_ofNat,
      show (9 : Word).toNat = 9 by decide,
      Nat.mod_eq_of_lt (by omega : q < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : q % 9 < 2 ^ 64)]

theorem div9 (q : Nat) (hq : q ≤ 192) :
    rv64_divu (BitVec.ofNat 64 q) 9 = BitVec.ofNat 64 (q / 9) := by
  apply BitVec.eq_of_toNat_eq
  unfold rv64_divu
  split
  · rename_i hz
    simp at hz
  · simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat,
      show (9 : Word).toNat = 9 by decide,
      Nat.mod_eq_of_lt (by omega : q < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : q / 9 < 2 ^ 64)]

#print axioms rem9
#print axioms div9

private theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp [MachineState.getByte, MachineState.getMem_setReg]
private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte, MachineState.getMem_setPC]
private theorem getReg_setByte (s : MachineState) (a : Word) (v : BitVec 8)
    (r : Reg) : (s.setByte a v).getReg r = s.getReg r := by
  simp [MachineState.setByte, MachineState.setMem]
  cases r <;> rfl

theorem tail_byte2 (s : MachineState) (q : Nat)
    (hq : q ≤ 192) (value : s.getReg .x23 = BitVec.ofNat 64 q)
    (ptr : s.getReg .x11 = 0x80640) :
    (tailState s).getByte 0x80642 = BitVec.ofNat 8 (q / 9) := by
  have haddr : s.getReg .x11 + 2 = (0x80642 : Word) := by rw [ptr]; decide
  rw [← haddr]
  simp [tailState, execInstrBr, getByte_setReg, getByte_setPC,
    Signing.getByte_setByte, getReg_setByte, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    signExtend12, value]
  simpa using congrArg (BitVec.setWidth 8) (div9 q hq)

#print axioms tail_byte2

theorem tail_byte1 (s : MachineState) (q : Nat)
    (hq : q ≤ 192) (value : s.getReg .x23 = BitVec.ofNat 64 q)
    (ptr : s.getReg .x11 = 0x80640) :
    (tailState s).getByte 0x80641 = BitVec.ofNat 8 (q % 9) := by
  have haddr : s.getReg .x11 + 1 = (0x80641 : Word) := by rw [ptr]; decide
  have hneq : s.getReg .x11 + 1 ≠ s.getReg .x11 + 2 := by rw [ptr]; decide
  rw [← haddr]
  simp [tailState, execInstrBr, getByte_setReg, getByte_setPC,
    Signing.getByte_setByte, getReg_setByte, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    signExtend12, value, hneq]
  simpa using congrArg (BitVec.setWidth 8) (rem9 q hq)

#print axioms tail_byte1

theorem tail_preserves_other (s : MachineState) (a : Word)
    (h1 : a ≠ s.getReg .x11 + 1)
    (h2 : a ≠ s.getReg .x11 + 2) :
    (tailState s).getByte a = s.getByte a := by
  simp [tailState, execInstrBr, getByte_setReg, getByte_setPC,
    Signing.getByte_setByte, getReg_setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12, h1, h2]
  split_ifs with ha hb
  · exact (h2 ha).elim
  · exact (h1 hb).elim
  · rfl

#print axioms tail_preserves_other

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTail67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCopyMem67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranch67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteBranchSteps67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTail67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67

theorem copyLoop_preserves_flag (s : MachineState)
    (output : s.getReg .x11 = 0x80600) (n : Nat) (hn : n ≤ 16) :
    (copyLoop s n).getByte 0x80640 = s.getByte 0x80640 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have hptr : (copyLoop s n).getReg .x11 =
        BitVec.ofNat 64 (0x80600+4*n) := by
      rw [copyLoop_output_pointer, output, BitVec.ofNat_add]
      rfl
    have hne : alignToDword (0x80640 : Word) ≠
        alignToDword ((copyLoop s n).getReg .x11) := by
      rw [hptr]
      interval_cases n <;> decide
    change (GroupedBalancedVerifyByteCopy67.copyBody (copyLoop s n)).getByte 0x80640 = _
    rw [copyBody_preserves_byte _ _ hne, ih hn0]

#print axioms copyLoop_preserves_flag

def selectedBranch (s : MachineState) (message : BitVec 128) : MachineState :=
  if GroupedBalancedQuaternary.rawSum message < 96 then
    smallBranch s else largeBranch s

theorem selectedBranch_steps (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (validFlag : accessValid (s.getReg .x11 + 64) 1 = true) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s
      (if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)
      (selectedBranch s message) := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simpa [selectedBranch, h] using
      smallBranch_steps s _ pc sum h validFlag
  · have hmax := GroupedBalancedQuaternary.rawSum_le message
    simpa [selectedBranch, h] using
      largeBranch_steps s _ pc sum (by omega) hmax validFlag

theorem selectedBranch_fields (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700) :
    (selectedBranch s message).pc = 0x1abc ∧
    (selectedBranch s message).getReg .x17 =
      (if GroupedBalancedQuaternary.rawSum message < 96 then 0xfffc00 else 0xfff800) ∧
    (selectedBranch s message).getReg .x18 = 16 ∧
    (selectedBranch s message).getReg .x23 =
      BitVec.ofNat 64 (GroupedBalancedByteSum67.decoderChecksum message) ∧
    (selectedBranch s message).getReg .x10 = s.getReg .x10 ∧
    (selectedBranch s message).getReg .x11 = s.getReg .x11 ∧
    (selectedBranch s message).getByte (s.getReg .x11 + 64) =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.flagDigit message) := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · have hf := smallBranch_fields s _ pc sum h stack
    simp only [selectedBranch, if_pos h]
    rcases hf with ⟨hfpc,hftab,hfrem,hfq,hfx10,hfx11⟩
    refine ⟨hfpc, ?_, hfrem, ?_, hfx10, hfx11, ?_⟩
    · simpa [h] using hftab
    · simpa [GroupedBalancedByteSum67.decoderChecksum,
        GroupedBalancedByteSum67.sumBytes_eq_rawSum, h] using hfq
    · simpa [GroupedBalancedQuaternary.flagDigit, h] using smallBranch_flag s
  · have hmax := GroupedBalancedQuaternary.rawSum_le message
    have hf := largeBranch_fields s _ pc sum (by omega) hmax stack
    simp only [selectedBranch, if_neg h]
    rcases hf with ⟨hfpc,hftab,hfrem,hfq,hfx10,hfx11⟩
    refine ⟨hfpc, ?_, hfrem, ?_, hfx10, hfx11, ?_⟩
    · simpa [h] using hftab
    · simpa [GroupedBalancedByteSum67.decoderChecksum,
        GroupedBalancedByteSum67.sumBytes_eq_rawSum, h] using hfq
    · simpa [GroupedBalancedQuaternary.flagDigit, h] using largeBranch_flag s

theorem selectedBranch_preserves_byte (s : MachineState)
    (message : BitVec 128) (a : Word)
    (hne : a ≠ s.getReg .x11 + 64) :
    (selectedBranch s message).getByte a = s.getByte a := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simpa [selectedBranch, h] using smallBranch_preserves_byte s a hne
  · simpa [selectedBranch, h] using largeBranch_preserves_byte s a hne

#print axioms selectedBranch_steps
#print axioms selectedBranch_fields
#print axioms selectedBranch_preserves_byte

def postSumState (s : MachineState) (message : BitVec 128) : MachineState :=
  tailState (copyLoop (selectedBranch s message) 16)

theorem postSum_steps (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s
      ((if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6)
      (postSumState s message) := by
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hvflag : accessValid (s.getReg .x11 + 64) 1 = true := by
    rw [output]
    decide
  have hstepb := selectedBranch_steps s message pc sum hvflag
  have hf := selectedBranch_fields s message pc sum stack
  rcases hf with ⟨hfpc,hftable,hfrem,hfx23,hfx10,hfx11,hfflag⟩
  have htable : b.getReg .x17 = 0xfff800 ∨ b.getReg .x17 = 0xfffc00 := by
    change (selectedBranch s message).getReg .x17 = _ ∨ _
    rw [hftable]
    split_ifs <;> simp
  have hstepc := copyLoop_interface_control b hfpc hfrem
    (by rw [hfx10, input]) (by rw [hfx11, output]) htable
  rcases hstepc with ⟨hsc,hcpc,hcx10,hcx11,hcx18,hcx17⟩
  have hv1 : accessValid (c.getReg .x11 + 1) 1 = true := by
    rw [hcx11]
    decide
  have hv2 : accessValid (c.getReg .x11 + 2) 1 = true := by
    rw [hcx11]
    decide
  have hst := tail_steps c hcpc hv1 hv2
  have hbc := steps_comp hstepb hsc
  have hbct := steps_comp hbc hst
  simpa only [postSumState, b, c, Nat.add_assoc] using hbct

#print axioms postSum_steps

theorem postSum_payload_bytes (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600)
    (hmsg : ∀ j : Fin 16,
      s.getByte (s.getReg .x10 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8)
    (hplain : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val))
    (hflip : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val)) :
    ∀ j : Fin 16, ∀ k : Fin 4,
      (postSumState s message).getByte
        (BitVec.ofNat 64 (0x80600+4*j.val+k.val)) =
          BitVec.ofNat 8 (GroupedBalancedQuaternary.payloadDigit message
            ⟨4*j.val+k.val, by omega⟩) := by
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hf := selectedBranch_fields s message pc sum stack
  rcases hf with ⟨hfpc,hftable,hfrem,hfx23,hfx10,hfx11,hfflag⟩
  have hmsg_b : ∀ j : Fin 16,
      b.getByte (b.getReg .x10 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8 := by
    intro j
    change (selectedBranch s message).getByte _ = _
    rw [hfx10]
    have hne : s.getReg .x10 + BitVec.ofNat 64 j.val ≠ s.getReg .x11 + 64 := by
      rw [input, output]
      fin_cases j <;> decide
    rw [selectedBranch_preserves_byte s message _ hne]
    exact hmsg j
  have hplain_b : ∀ entry : Fin 256, ∀ k : Fin 4,
      b.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val) := by
    intro entry k
    have hne : BitVec.ofNat 64 (0xfff800+4*entry.val+k.val) ≠ s.getReg .x11 + 64 := by
      rw [output]
      intro he
      have hn := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0xfff800+4*entry.val+k.val < 2 ^ 64),
        show ((0x80600 : Word) + 64).toNat = 0x80640 by decide] at hn
      omega
    rw [selectedBranch_preserves_byte s message _ hne]
    exact hplain entry k
  have hflip_b : ∀ entry : Fin 256, ∀ k : Fin 4,
      b.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val) := by
    intro entry k
    have hne : BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val) ≠ s.getReg .x11 + 64 := by
      rw [output]
      intro he
      have hn := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0xfffc00+4*entry.val+k.val < 2 ^ 64),
        show ((0x80600 : Word) + 64).toNat = 0x80640 by decide] at hn
      omega
    rw [selectedBranch_preserves_byte s message _ hne]
    exact hflip entry k
  have hcp11 : c.getReg .x11 = 0x80640 := by
    rw [copyLoop_output_pointer, hfx11, output]
    decide
  intro j k
  let a : Word := BitVec.ofNat 64 (0x80600+4*j.val+k.val)
  have hne1 : a ≠ c.getReg .x11 + 1 := by
    rw [hcp11]
    intro he
    have hn := congrArg BitVec.toNat he
    simp only [a, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80600+4*j.val+k.val < 2 ^ 64),
      show ((0x80640 : Word) + 1).toNat = 0x80641 by decide] at hn
    omega
  have hne2 : a ≠ c.getReg .x11 + 2 := by
    rw [hcp11]
    intro he
    have hn := congrArg BitVec.toNat he
    simp only [a, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80600+4*j.val+k.val < 2 ^ 64),
      show ((0x80640 : Word) + 2).toNat = 0x80642 by decide] at hn
    omega
  change (tailState c).getByte a = _
  rw [tail_preserves_other c a hne1 hne2]
  exact GroupedBalancedVerifyBytePayload67.output_payload_bytes b message
    (by rw [hfx10, input]) (by rw [hfx11, output]) hftable
    hmsg_b hplain_b hflip_b j k

#print axioms postSum_payload_bytes

private theorem getReg_setWord32 (s : MachineState) (a : Word) (v : BitVec 32)
    (r : Reg) : (s.setWord32 a v).getReg r = s.getReg r := by
  simp [MachineState.setWord32, MachineState.setMem]
  cases r <;> rfl

theorem copyBody_x23 (s : MachineState) :
    (GroupedBalancedVerifyByteCopy67.copyBody s).getReg .x23 = s.getReg .x23 := by
  simp [GroupedBalancedVerifyByteCopy67.copyBody, execInstrBr,
    getReg_setWord32, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, signExtend12]

theorem copyLoop_x23 (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x23 = s.getReg .x23 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copyLoop, copyBody_x23] using ih

#print axioms copyLoop_x23

theorem postSum_flag (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (output : s.getReg .x11 = 0x80600) :
    (postSumState s message).getByte 0x80640 =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.flagDigit message) := by
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hf := selectedBranch_fields s message pc sum stack
  rcases hf with ⟨hfpc,hftable,hfrem,hfx23,hfx10,hfx11,hfflag⟩
  have hptr : c.getReg .x11 = 0x80640 := by
    rw [copyLoop_output_pointer, hfx11, output]
    decide
  have hne1 : (0x80640 : Word) ≠ c.getReg .x11 + 1 := by
    rw [hptr]
    decide
  have hne2 : (0x80640 : Word) ≠ c.getReg .x11 + 2 := by
    rw [hptr]
    decide
  change (tailState c).getByte 0x80640 = _
  rw [tail_preserves_other c _ hne1 hne2,
    copyLoop_preserves_flag b (by rw [hfx11, output]) 16 (by decide)]
  simpa [output] using hfflag

#print axioms postSum_flag

theorem decoderChecksum_le (message : BitVec 128) :
    GroupedBalancedByteSum67.decoderChecksum message ≤ 192 := by
  have hsum := GroupedBalancedQuaternary.rawSum_le message
  simp only [GroupedBalancedByteSum67.decoderChecksum,
    GroupedBalancedByteSum67.sumBytes_eq_rawSum]
  split_ifs <;> omega

#print axioms decoderChecksum_le

theorem postSum_checksum_bytes (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (output : s.getReg .x11 = 0x80600) :
    (postSumState s message).getByte 0x80641 =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.checksum message % 9) ∧
    (postSumState s message).getByte 0x80642 =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.checksum message / 9) := by
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hf := selectedBranch_fields s message pc sum stack
  rcases hf with ⟨hfpc,hftable,hfrem,hfx23,hfx10,hfx11,hfflag⟩
  have hptr : c.getReg .x11 = 0x80640 := by
    rw [copyLoop_output_pointer, hfx11, output]
    decide
  have hval : c.getReg .x23 =
      BitVec.ofNat 64 (GroupedBalancedByteSum67.decoderChecksum message) := by
    rw [copyLoop_x23]
    exact hfx23
  have hq := decoderChecksum_le message
  change (tailState c).getByte 0x80641 =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.checksum message % 9) ∧
    (tailState c).getByte 0x80642 =
      BitVec.ofNat 8 (GroupedBalancedQuaternary.checksum message / 9)
  rw [← GroupedBalancedByteSum67.decoderChecksum_eq message]
  exact ⟨tail_byte1 c _ hq hval hptr, tail_byte2 c _ hq hval hptr⟩

#print axioms postSum_checksum_bytes

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67
