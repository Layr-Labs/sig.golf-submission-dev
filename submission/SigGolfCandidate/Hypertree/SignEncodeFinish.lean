import SigGolfCandidate.Hypertree.SignEncode
import SigGolfCandidate.Hypertree.KeygenControl

/-! Inlined from SigGolfCandidate.Hypertree.SignEncodeLoop; its only importer was SigGolfCandidate.Hypertree.SignEncodeFinish. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def encodeDigit (message : BitVec 128) (i : Nat) : Nat := message.toNat / 8 ^ i % 8

def encodeSum (message : BitVec 128) (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, encodeDigit message i

theorem encodeDigit_lt (message : BitVec 128) (i : Nat) : encodeDigit message i < 8 :=
  Nat.mod_lt _ (by decide)

theorem encodeSum_succ (message : BitVec 128) (n : Nat) :
    encodeSum message (n + 1) = encodeSum message n + encodeDigit message n := by
  exact Finset.sum_range_succ _ _

theorem encode_shift_low (value : BitVec 128) :
    (value.extractLsb' 0 64 >>> 3) + (value.extractLsb' 64 64 <<< 61) =
      (value >>> 3).extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem encode_shift_high (value : BitVec 128) :
    (value.extractLsb' 64 64 >>> 3) = (value >>> 3).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := value.isLt
  simp [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem encode_digit_limb (message : BitVec 128) (i : Nat) :
    (message >>> (3 * i)).extractLsb' 0 64 &&& 7 = BitVec.ofNat 64 (encodeDigit message i) := by
  apply BitVec.eq_of_toNat_eq
  have small := encodeDigit_lt message i
  have power : 8 ^ i = 2 ^ (3 * i) := by rw [show (8 : Nat) = 2 ^ 3 by decide, Nat.pow_mul]
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
  change ((message.toNat / 2 ^ (3 * i)) % 2 ^ 64) &&& 7 = _
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [show 2 ^ 3 = (8 : Nat) by decide]
  unfold encodeDigit at small ⊢
  rw [power]
  omega

/-- The running digest is shifted by three bits per completed message digit. -/
def EncodeInvariant (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState) : Prop :=
  n ≤ 43 ∧ s.pc = (if n = 0 then base + 40 else base) ∧
  s.getReg .x6 = (message >>> (3 * (43 - n))).extractLsb' 0 64 ∧
  s.getReg .x7 = (message >>> (3 * (43 - n))).extractLsb' 64 64 ∧
  s.getReg .x10 = BitVec.ofNat 64 (0x80600 + (43 - n)) ∧
  s.getReg .x11 = BitVec.ofNat 64 n ∧
  s.getReg .x12 = 301 - BitVec.ofNat 64 (encodeSum message (43 - n))

def EncodedPrefix (message : BitVec 128) (n : Nat) (s : MachineState) : Prop :=
  ∀ i, i < 43 - n → s.getByte (BitVec.ofNat 64 (0x80600 + i)) = BitVec.ofNat 8 (encodeDigit message i)

theorem encode_next_invariant (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message (n + 1) s) : EncodeInvariant base message n (encodeNext s) := by
  obtain ⟨hn, pc, lo, hi, ptr, count, sum⟩ := inv
  have processed : 43 - n = (43 - (n + 1)) + 1 := by omega
  have shift : message >>> (3 * (43 - n)) = (message >>> (3 * (43 - (n + 1)))) >>> 3 := by
    rw [processed, Nat.mul_add, Nat.mul_one, BitVec.shiftRight_add]
  have hc : BitVec.ofNat 64 (n + 1) = 1 ↔ n = 0 := by
    constructor
    · intro eq
      have value := congrArg BitVec.toNat eq
      change (n + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt (by omega)] at value
      omega
    · intro eq; subst n; rfl
  obtain ⟨rlo, rhi, rptr, rcount, rsum⟩ := encodeNext_regs s
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : s.pc = base := by simpa using pc
    rw [encodeNext_pc, hp, count]
    simp only [hc]
  · rw [rlo, lo, hi, shift]
    exact encode_shift_low _
  · rw [rhi, hi, shift]
    exact encode_shift_high _
  · rw [rptr, ptr, processed]
    change BitVec.ofNat 64 (0x80600 + (43 - (n + 1))) + BitVec.ofNat 64 1 = _
    rw [← BitVec.ofNat_add]
    congr 1
  · rw [rcount, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  · rw [rsum, sum, lo, encode_digit_limb, processed, encodeSum_succ, BitVec.ofNat_add]
    exact BitVec.sub_sub _ _ _

theorem encode_next_prefix (base : Word) (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message (n + 1) s) (outputPrefix : EncodedPrefix message (n + 1) s) :
    EncodedPrefix message n (encodeNext s) := by
  obtain ⟨hn, _, lo, _, ptr, _, _⟩ := inv
  intro i hi
  by_cases eq : i = 43 - (n + 1)
  · subst i
    rw [encodeNext_byte, ptr, if_pos rfl, lo, encode_digit_limb]
    simp
  · have ne : BitVec.ofNat 64 (0x80600 + i) ≠ BitVec.ofNat 64 (0x80600 + (43 - (n + 1))) := by
      intro he
      have values := congrArg BitVec.toNat he
      have h1 : 0x80600 + i < 2 ^ 64 := by omega
      have h2 : 0x80600 + (43 - (n + 1)) < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at values
      omega
    rw [encodeNext_byte, ptr, if_neg ne]
    exact outputPrefix i (by omega)

theorem encode_loop (image : Image) (base : Word) (code : EncodeLoopCode image base)
    (message : BitVec 128) (n : Nat) (s : MachineState)
    (inv : EncodeInvariant base message n s) (outputPrefix : EncodedPrefix message n s) :
    ∃ final, OrdinarySteps image s (10 * n) final ∧ EncodeInvariant base message 0 final ∧
      EncodedPrefix message 0 final ∧
      (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) → final.getByte a = s.getByte a) ∧ final.getReg .x2 = s.getReg .x2 := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv, outputPrefix, (fun _ _ => rfl), rfl⟩
  | succ n ih =>
    have hn := inv.1
    have pc : s.pc = base := by simpa using inv.2.1
    have valid : accessValid (s.getReg .x10) 1 = true := by
      rw [inv.2.2.2.2.1]
      simp [accessValid, rangeValid, MEMORY_BYTES]
      omega
    obtain ⟨final, tail, finalInv, output, frame, stack⟩ := ih (encodeNext s)
      (encode_next_invariant base message n s inv) (encode_next_prefix base message n s inv outputPrefix)
    refine ⟨final, ?_, finalInv, output, ?_, ?_⟩
    · simpa only [Nat.mul_add, Nat.mul_one] using Keygen.ordinary_trans image s _ final 10 (10 * n)
        (encodeNext_block image base code s pc valid) tail
    · intro a outside
      rw [frame a outside, encodeNext_byte, inv.2.2.2.2.1,
        if_neg (outside ⟨43 - (n + 1), by omega⟩)]
    · exact stack.trans (encodeNext_sp s)

theorem encodeSum_reference (message : Reference.Digest) :
    encodeSum message 43 = ∑ i : Fin 43, Reference.messageDigit message i := by
  rw [encodeSum, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem encodeSum_bound (message : BitVec 128) : encodeSum message 43 ≤ 301 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range 43, (7 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      have := encodeDigit_lt message i
      omega
    _ = 301 := by simp

/-- The complete 43-round message-digit loop terminates in exactly 430 ordinary
instructions, stores the raw digits, and computes their raw checksum. -/
theorem encode_message_refines (image : Image) (base : Word) (code : EncodeLoopCode image base)
    (message : Reference.Digest) (s : MachineState)
    (pc : s.pc = base)
    (lo : s.getReg .x6 = message.extractLsb' 0 64)
    (hi : s.getReg .x7 = message.extractLsb' 64 64)
    (ptr : s.getReg .x10 = 0x80600) (count : s.getReg .x11 = 43)
    (checksum : s.getReg .x12 = 301) :
    ∃ final, OrdinarySteps image s 430 final ∧ final.pc = base + 40 ∧
      final.getReg .x10 = 0x8062b ∧
      final.getReg .x12 = BitVec.ofNat 64 (301 - Reference.rawSum message) ∧
      (∀ i : Fin 43, final.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i)) ∧
      (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600 + i.val)) → final.getByte a = s.getByte a) ∧ final.getReg .x2 = s.getReg .x2 := by
  have initial : EncodeInvariant base message 43 s := by
    simp [EncodeInvariant, pc, lo, hi, ptr, count, checksum, encodeSum]
  have empty : EncodedPrefix message 43 s := by intro i h; omega
  obtain ⟨final, trace, inv, output, frame, stack⟩ := encode_loop image base code message 43 s initial empty
  refine ⟨final, trace, by simpa using inv.2.1, by simpa using inv.2.2.2.2.1, ?_, ?_, frame, stack⟩
  · rw [inv.2.2.2.2.2.2]
    have bound := encodeSum_bound message
    change BitVec.ofNat 64 301 - BitVec.ofNat 64 (encodeSum message 43) = _
    rw [BitVec.ofNat_sub_ofNat_of_le 301 (encodeSum message 43) (by omega) bound,
      encodeSum_reference]
    rfl
  · intro i
    exact output i.val (by have := i.isLt; omega)

/-- info: 'SigGolfCandidate.Hypertree.Signing.encode_message_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_message_refines

end SigGolfCandidate.Hypertree.Signing
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

@[simp] theorem reg_setByte (s : MachineState) (a : Word) (b : Byte) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by simp [MachineState.setByte]

@[simp] theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by simp [MachineState.getByte]

def checksumState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 0)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 1)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 2)
  execInstrBr s (.SRLI .x12 .x12 3)

def checksumInstructions : List Instr := [
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 0,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 1,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 2,
  .SRLI .x12 .x12 3]

def ChecksumCode (image : Image) (base : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 9), s.pc = base + BitVec.ofNat 64 (4 * i.val) →
    fetch image s = some (.base (checksumInstructions[i.val]'(by simp [checksumInstructions])))

theorem checksumState_block (image : Image) (base : Word) (code : ChecksumCode image base)
    (s : MachineState) (pc : s.pc = base) (ptr : s.getReg .x10 = 0x8062b) :
    OrdinarySteps image s 9 (checksumState s) := by
  let s1 := execInstrBr s (.ANDI .x13 .x12 7)
  let s2 := execInstrBr s1 (.SB .x10 .x13 0)
  let s3 := execInstrBr s2 (.SRLI .x12 .x12 3)
  let s4 := execInstrBr s3 (.ANDI .x13 .x12 7)
  let s5 := execInstrBr s4 (.SB .x10 .x13 1)
  let s6 := execInstrBr s5 (.SRLI .x12 .x12 3)
  let s7 := execInstrBr s6 (.ANDI .x13 .x12 7)
  let s8 := execInstrBr s7 (.SB .x10 .x13 2)
  let s9 := execInstrBr s8 (.SRLI .x12 .x12 3)
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x13 .x12 7)) 8
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SB .x10 .x13 0)) 7
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.SRLI .x12 .x12 3)) 6
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x13 .x12 7)) 5
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SB .x10 .x13 1)) 4
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.SRLI .x12 .x12 3)) 3
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ANDI .x13 .x12 7)) 2
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SB .x10 .x13 2)) 1
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.SRLI .x12 .x12 3)) 0
  · apply code _ 8
    simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem checksumState_pc (s : MachineState) : (checksumState s).pc = s.pc + 36 := by
  simp [checksumState, execInstrBr, BitVec.add_assoc]

theorem checksumState_sp (s : MachineState) : (checksumState s).getReg .x2 = s.getReg .x2 := by
  simp [checksumState, execInstrBr, MachineState.getReg_setReg_ne]

theorem checksumState_byte (s : MachineState) (a : Word) :
    (checksumState s).getByte a =
      if a = s.getReg .x10 + 2 then ((s.getReg .x12 >>> 6) &&& 7).truncate 8 else
      if a = s.getReg .x10 + 1 then ((s.getReg .x12 >>> 3) &&& 7).truncate 8 else
      if a = s.getReg .x10 then (s.getReg .x12 &&& 7).truncate 8 else s.getByte a := by
  simp [checksumState, execInstrBr, signExtend12, getByte_setByte, Memory.getByte_setReg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ← BitVec.shiftRight_add]

theorem checksum_digit (checksum : Nat) (bound : checksum ≤ 301) (i : Fin 3) :
    ((BitVec.ofNat 64 checksum >>> (3 * i.val)) &&& 7).truncate 8 =
      BitVec.ofNat 8 (checksum / 8 ^ i.val % 8) := by
  apply BitVec.eq_of_toNat_eq
  have small : checksum < 2 ^ 64 := by omega
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.shiftRight_eq_div_pow]
  change (checksum / 2 ^ (3 * i.val) &&& 7) % 2 ^ 8 = _
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  fin_cases i <;> simp

theorem checksumState_output (s : MachineState) (checksum : Nat) (bound : checksum ≤ 301)
    (ptr : s.getReg .x10 = 0x8062b) (value : s.getReg .x12 = BitVec.ofNat 64 checksum)
    (i : Fin 3) :
    (checksumState s).getByte (BitVec.ofNat 64 (0x8062b + i.val)) =
      BitVec.ofNat 8 (checksum / 8 ^ i.val % 8) := by
  fin_cases i
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 0
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 1
  · simpa [checksumState_byte, ptr, value] using checksum_digit checksum bound 2

theorem checksumState_frame (s : MachineState) (ptr : s.getReg .x10 = 0x8062b)
    (a : Word) (outside : ∀ i : Fin 3, a ≠ BitVec.ofNat 64 (0x8062b + i.val)) :
    (checksumState s).getByte a = s.getByte a := by
  have h0 : a ≠ 0x8062b := outside 0
  have h1 : a ≠ 0x8062c := outside 1
  have h2 : a ≠ 0x8062d := outside 2
  rw [checksumState_byte, ptr]
  change (if a = 0x8062d then _ else if a = 0x8062c then _ else if a = 0x8062b then _ else _) = _
  rw [if_neg h2, if_neg h1, if_neg h0]

theorem digit_address_ne (i j : Nat) (hi : i < 46) (hj : j < 46) (ne : i ≠ j) :
    BitVec.ofNat 64 (0x80600 + i) ≠ BitVec.ofNat 64 (0x80600 + j) := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have h1 : 0x80600 + i < 2 ^ 64 := by omega
  have h2 : 0x80600 + j < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at values
  omega

/-- Completing the three checksum digits yields every one of the reference's 46 digits. -/
theorem checksumState_refines (s : MachineState) (message : Reference.Digest)
    (ptr : s.getReg .x10 = 0x8062b)
    (value : s.getReg .x12 = BitVec.ofNat 64 (Reference.checksum message))
    (digits : ∀ i : Fin 43, s.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
      BitVec.ofNat 8 (Reference.payloadDigit message i)) :
    ∀ i : Reference.Chain, (checksumState s).getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
      BitVec.ofNat 8 (Reference.digit message i).val := by
  intro i
  by_cases small : i.val < 43
  · rw [checksumState_frame s ptr, digits ⟨i.val, small⟩]
    · have rawLt : Reference.messageDigit message ⟨i.val, small⟩ < 8 := by
        unfold Reference.messageDigit
        exact Nat.mod_lt _ (by decide)
      have payloadLt : Reference.payloadDigit message ⟨i.val, small⟩ < 8 := by
        unfold Reference.payloadDigit
        split_ifs <;> omega
      simpa [Reference.digit, small, Nat.mod_eq_of_lt small,
        Nat.mod_eq_of_lt payloadLt]
    · intro j
      have hj := j.isLt
      have eq : 0x8062b + j.val = 0x80600 + (43 + j.val) := by omega
      rw [eq]
      exact digit_address_ne i.val (43 + j.val) i.isLt (by omega) (by omega)
  · have hj : i.val - 43 < 3 := by have := i.isLt; omega
    have bound : Reference.checksum message ≤ 301 := Nat.sub_le _ _
    have output := checksumState_output s (Reference.checksum message) bound ptr value ⟨i.val - 43, hj⟩
    have addr : 0x8062b + (i.val - 43) = 0x80600 + i.val := by omega
    simpa [addr, Reference.digit, small] using output

end SigGolfCandidate.Hypertree.Signing
