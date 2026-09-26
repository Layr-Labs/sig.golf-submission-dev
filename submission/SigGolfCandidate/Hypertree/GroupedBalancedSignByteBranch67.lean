import SigGolfCandidate.Hypertree.GroupedBalancedSignByteWordBridge67
import SigGolfCandidate.Hypertree.SignEncode

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBytePayload67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteOutputs67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteWordBridge67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBytePayload67

theorem source_address_formula (s : MachineState) (j : Fin 16) (k : Fin 4)
    (table : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00) :
    sourceTableAddr s j.val + BitVec.ofNat 64 k.val =
      BitVec.ofNat 64 ((s.getReg .x17).toNat +
        4*(s.getByte (s.getReg .x10 + BitVec.ofNat 64 j.val)).toNat + k.val) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, sourceTableAddr_toNat s j.val table]
  simp only [BitVec.toNat_ofNat]
  have hbase : (s.getReg .x17).toNat = 0xfff800 ∨
      (s.getReg .x17).toNat = 0xfffc00 := by
    rcases table with h | h <;> rw [h] <;> simp
  have hb := (s.getByte (s.getReg .x10 + BitVec.ofNat 64 j.val)).isLt
  rw [Nat.mod_eq_of_lt (by omega : k.val < 2 ^ 64)]

theorem output_payload_bytes (s : MachineState) (message : BitVec 128)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600)
    (table : s.getReg .x17 =
      if GroupedBalancedQuaternary.rawSum message < 96 then 0xfffc00 else 0xfff800)
    (hmsg : ∀ j : Fin 16,
      s.getByte (s.getReg .x10 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8)
    (hplain : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (rawByteDigit entry.val k.val))
    (hflip : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-rawByteDigit entry.val k.val)) :
    ∀ j : Fin 16, ∀ k : Fin 4,
      (copyLoop s 16).getByte
        (BitVec.ofNat 64 (0x80600+4*j.val+k.val)) =
          BitVec.ofNat 8 (GroupedBalancedQuaternary.payloadDigit message
            ⟨4*j.val+k.val, by omega⟩) := by
  intro j k
  have htable : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00 := by
    rw [table]
    split_ifs <;> simp
  rw [copyLoop_output_bytes s input output htable j k,
    source_address_formula s j k htable, hmsg j]
  let entry : Fin 256 := ⟨(message.extractLsb' (8*j.val) 8).toNat,
    (message.extractLsb' (8*j.val) 8).isLt⟩
  by_cases hsmall : GroupedBalancedQuaternary.rawSum message < 96
  · have ht : s.getReg .x17 = 0xfffc00 := by simpa [hsmall] using table
    rw [ht]
    simp only [show (0xfffc00 : Word).toNat = 0xfffc00 by decide]
    have hd := selected_byte_digit message j k
    simp only [if_pos hsmall] at hd
    simpa only [entry] using
      (hflip entry k).trans (congrArg (BitVec.ofNat 8)
        hd)
  · have ht : s.getReg .x17 = 0xfff800 := by simpa [hsmall] using table
    rw [ht]
    simp only [show (0xfff800 : Word).toNat = 0xfff800 by decide]
    have hd := selected_byte_digit message j k
    simp only [if_neg hsmall] at hd
    simpa only [entry] using
      (hplain entry k).trans (congrArg (BitVec.ofNat 8)
        hd)

#print axioms output_payload_bytes

end SigGolfCandidate.Hypertree.GroupedBalancedSignBytePayload67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67

def branchPrefix (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.SLTIU .x16 .x14 96)) (.BEQ .x16 .x0 16)

def commonBranch (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x17 .x2 256)
  let s := execInstrBr s (.SLLI .x20 .x16 10)
  let s := execInstrBr s (.ADD .x17 .x17 .x20)
  execInstrBr s (.ADDI .x18 .x0 16)

def smallBranch (s : MachineState) : MachineState :=
  let s := branchPrefix s
  let s := execInstrBr s (.SB .x11 .x0 64)
  let s := execInstrBr s (.ADDI .x23 .x14 3)
  let s := execInstrBr s (.JAL .x0 20)
  commonBranch s

def largeBranch (s : MachineState) : MachineState :=
  let s := branchPrefix s
  let s := execInstrBr s (.ADDI .x24 .x0 3)
  let s := execInstrBr s (.SB .x11 .x24 64)
  let s := execInstrBr s (.ADDI .x23 .x0 192)
  let s := execInstrBr s (.SUB .x23 .x23 .x14)
  commonBranch s

theorem smallBranch_fields (s : MachineState) (n : Nat)
    (pc : s.pc = 0x2134) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nsmall : n < 96) (stack : s.getReg .x2 = 0xfff700) :
    (smallBranch s).pc = 0x2168 ∧
    (smallBranch s).getReg .x17 = 0xfffc00 ∧
    (smallBranch s).getReg .x18 = 16 ∧
    (smallBranch s).getReg .x23 = BitVec.ofNat 64 (n+3) ∧
    (smallBranch s).getReg .x10 = s.getReg .x10 ∧
    (smallBranch s).getReg .x11 = s.getReg .x11 := by
  have hmod : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  simp [smallBranch, commonBranch, branchPrefix, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC, MachineState.setByte,
    pc, sum, stack, signExtend12,
    BitVec.ult, BitVec.ofNat_add, signExtend13, signExtend21]
  simp only [show n % 18446744073709551616 = n from hmod,
    not_le.mpr nsmall, if_false, if_pos nsmall]
  decide

#print axioms smallBranch_fields

theorem largeBranch_fields (s : MachineState) (n : Nat)
    (pc : s.pc = 0x2134) (sum : s.getReg .x14 = BitVec.ofNat 64 n)
    (nbig : 96 ≤ n) (nmax : n ≤ 192) (stack : s.getReg .x2 = 0xfff700) :
    (largeBranch s).pc = 0x2168 ∧
    (largeBranch s).getReg .x17 = 0xfff800 ∧
    (largeBranch s).getReg .x18 = 16 ∧
    (largeBranch s).getReg .x23 = BitVec.ofNat 64 (192-n) ∧
    (largeBranch s).getReg .x10 = s.getReg .x10 ∧
    (largeBranch s).getReg .x11 = s.getReg .x11 := by
  have hmod : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  simp [largeBranch, commonBranch, branchPrefix, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getReg_setPC, MachineState.setByte,
    pc, sum, stack, signExtend12,
    BitVec.ult, signExtend13]
  simp only [show n % 18446744073709551616 = n from hmod,
    if_neg (show ¬n < 96 by omega), if_pos nbig]
  constructor
  · decide
  constructor
  · decide
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

#print axioms largeBranch_fields

private theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp [MachineState.getByte, MachineState.getMem_setReg]

private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte, MachineState.getMem_setPC]

theorem smallBranch_flag (s : MachineState) :
    (smallBranch s).getByte (s.getReg .x11 + 64) = 0 := by
  simp [smallBranch, commonBranch, branchPrefix, execInstrBr,
    Signing.getByte_setByte, getByte_setReg, getByte_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]

theorem largeBranch_flag (s : MachineState) :
    (largeBranch s).getByte (s.getReg .x11 + 64) = 3 := by
  simp [largeBranch, commonBranch, branchPrefix, execInstrBr,
    Signing.getByte_setByte, getByte_setReg, getByte_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]

#print axioms smallBranch_flag
#print axioms largeBranch_flag

private theorem branchPrefix_byte (s : MachineState) (a : Word) :
    (branchPrefix s).getByte a = s.getByte a := by
  unfold branchPrefix
  simp only [execInstrBr]
  split_ifs <;> simp [getByte_setReg, getByte_setPC]

private theorem branchPrefix_x11 (s : MachineState) :
    (branchPrefix s).getReg .x11 = s.getReg .x11 := by
  simp [branchPrefix, execInstrBr, MachineState.getReg_setReg_ne]

theorem smallBranch_preserves_byte (s : MachineState) (a : Word)
    (hne : a ≠ s.getReg .x11 + 64) :
    (smallBranch s).getByte a = s.getByte a := by
  simp [smallBranch, commonBranch, execInstrBr,
    Signing.getByte_setByte, getByte_setReg, getByte_setPC,
    branchPrefix_byte, branchPrefix_x11,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  intro h
  exact (hne h).elim

theorem largeBranch_preserves_byte (s : MachineState) (a : Word)
    (hne : a ≠ s.getReg .x11 + 64) :
    (largeBranch s).getByte a = s.getByte a := by
  simp [largeBranch, commonBranch, execInstrBr,
    Signing.getByte_setByte, getByte_setReg, getByte_setPC,
    branchPrefix_byte, branchPrefix_x11,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  intro h
  exact (hne h).elim

#print axioms smallBranch_preserves_byte
#print axioms largeBranch_preserves_byte

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteBranch67
