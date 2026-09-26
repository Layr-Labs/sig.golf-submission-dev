import SigGolfCandidate.Hypertree.GroupedBalancedSignByteSources67
import SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignByteOutputs67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteWordBridge67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteSources67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteOutputs67

def outputAddr (i : Fin 16) : Word := BitVec.ofNat 64 (0x80600+4*i.val)

def sourceTableAddr (s : MachineState) (n : Nat) : Word :=
  s.getReg .x17 + (BitVec.setWidth 64
    (s.getByte (s.getReg .x10 + BitVec.ofNat 64 n)) <<< 2)

theorem output_slots_sep (i j : Fin 16) (hne : i ≠ j) :
    alignToDword (outputAddr i) ≠ alignToDword (outputAddr j) ∨
      byteOffset (outputAddr i) / 4 ≠ byteOffset (outputAddr j) / 4 := by
  fin_cases i <;> fin_cases j <;> simp_all [outputAddr] <;> decide

theorem sourceTableAddr_lower (s : MachineState) (n : Nat)
    (htable : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00) :
    0xfff800 ≤ (sourceTableAddr s n).toNat := by
  let t := s.setReg .x10 (s.getReg .x10 + BitVec.ofNat 64 n)
  have hbase : t.getReg .x17 = 0xfff800 ∨ t.getReg .x17 = 0xfffc00 := by
    simpa [t, MachineState.getReg_setReg_ne] using htable
  have h := tableAddr_lower t hbase
  simpa [tableAddr, sourceTableAddr, t, MachineState.getByte,
    MachineState.getMem_setReg, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne] using h

theorem currentTableAddr_eq_source (s : MachineState) (n : Nat) (hn : n < 16)
    (input : s.getReg .x10 = 0x80500) (output : s.getReg .x11 = 0x80600) :
    tableAddr (copyLoop s n) = sourceTableAddr s n := by
  unfold tableAddr sourceTableAddr
  rw [copyLoop_table_pointer, copyLoop_input_pointer]
  have haddr : sourceAddress (s.getReg .x10 + BitVec.ofNat 64 n) := by
    left
    rw [input]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      show (0x80500 : Word).toNat = 0x80500 by decide,
      show n % 2 ^ 64 = n from Nat.mod_eq_of_lt (by omega)]
    omega
  rw [copyLoop_preserves_source_byte s output n (by omega) _ haddr]

theorem copyLoop_output_words (s : MachineState)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600)
    (table : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00)
    (n : Nat) (hn : n ≤ 16) (j : Fin 16) (hj : j.val < n) :
    (copyLoop s n).getWord32 (outputAddr j) =
      s.getWord32 (sourceTableAddr s j.val) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    let t := copyLoop s n
    have hptr : t.getReg .x11 = outputAddr ⟨n,hn1⟩ := by
      simp only [t, copyLoop_output_pointer, output, outputAddr]
      rw [BitVec.ofNat_add]
      rfl
    by_cases hlast : j.val = n
    · have heq : j = ⟨n,hn1⟩ := Fin.ext hlast
      subst j
      change (copyBody t).getWord32 (outputAddr ⟨n,hn1⟩) = _
      rw [← hptr, copyBody_output_word]
      change t.getWord32 (tableAddr t) =
        s.getWord32 (sourceTableAddr s n)
      rw [show tableAddr t = sourceTableAddr s n by
        simpa [t] using currentTableAddr_eq_source s n hn1 input output]
      have hsource : sourceAddress (sourceTableAddr s n) :=
        Or.inr (sourceTableAddr_lower s n table)
      rw [copyLoop_preserves_source_word s output n hn0 _ hsource]
    · have hj0 : j.val < n := by omega
      have hne : j ≠ ⟨n,hn1⟩ := by
        intro h
        exact hlast (congrArg Fin.val h)
      have hsep := output_slots_sep j ⟨n,hn1⟩ hne
      change (copyBody t).getWord32 (outputAddr j) = _
      rw [copyBody_preserves_word t (outputAddr j) (by simpa [hptr] using hsep)]
      exact ih hn0 j hj0

#print axioms copyLoop_output_words

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteOutputs67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteOutputs67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteSources67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteWordBridge67

theorem extractByte_word32 (w : Word) (p : Fin 2) (k : Fin 4) :
    extractByte w (4*p.val+k.val) =
      ((extractWord32 w p.val) >>> (8*k.val)).truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have hi32 : 8*k.val+i < 32 := by omega
  simp only [show i < 8 from hi, show 8*k.val+i < 32 from hi32,
    decide_true, Bool.true_and]
  congr 1
  omega

#print axioms extractByte_word32

theorem byteOffset_eq_mod (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod a.toNat 3

theorem aligned4_getByte_word32 (s : MachineState) (a : Word) (k : Fin 4)
    (ha : a.toNat % 4 = 0) (_hbound : a.toNat + 3 < 2 ^ 64) :
    s.getByte (a + BitVec.ofNat 64 k.val) =
      ((s.getWord32 a) >>> (8*k.val)).truncate 8 := by
  have haddr : (a + BitVec.ofNat 64 k.val).toNat = a.toNat + k.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k.val < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hoff : byteOffset (a + BitVec.ofNat 64 k.val) =
      4 * (byteOffset a / 4) + k.val := by
    rw [byteOffset_eq_mod, byteOffset_eq_mod, haddr]
    omega
  have halign : alignToDword (a + BitVec.ofNat 64 k.val) = alignToDword a := by
    apply BitVec.eq_of_toNat_eq
    have h0 := align_add_offset_toNat a
    have h1 := align_add_offset_toNat (a + BitVec.ofNat 64 k.val)
    rw [haddr, hoff] at h1
    have hb := byteOffset_lt_8 (addr := a)
    rw [byteOffset_eq_mod] at hb h0 h1
    omega
  rw [MachineState.getByte, MachineState.getWord32, halign, hoff]
  exact extractByte_word32 (s.getMem (alignToDword a))
    ⟨byteOffset a / 4, by have hb := byteOffset_lt_8 (addr := a); omega⟩ k

#print axioms aligned4_getByte_word32

theorem sourceTableAddr_toNat (s : MachineState) (n : Nat)
    (htable : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00) :
    (sourceTableAddr s n).toNat =
      (s.getReg .x17).toNat + 4 * (s.getByte
        (s.getReg .x10 + BitVec.ofNat 64 n)).toNat := by
  unfold sourceTableAddr
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have hb := (s.getByte (s.getReg .x10 + BitVec.ofNat 64 n)).isLt
  rcases htable with h | h <;> rw [h] <;>
    simp only [show (0xfff800 : Word).toNat = 0xfff800 by decide,
      show (0xfffc00 : Word).toNat = 0xfffc00 by decide] <;>
    omega

theorem copyLoop_output_bytes (s : MachineState)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600)
    (table : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00)
    (j : Fin 16) (k : Fin 4) :
    (copyLoop s 16).getByte
      (BitVec.ofNat 64 (0x80600+4*j.val+k.val)) =
    s.getByte (sourceTableAddr s j.val + BitVec.ofNat 64 k.val) := by
  have hword := copyLoop_output_words s input output table 16 (by omega) j j.isLt
  have hj := j.isLt
  have houtput : (outputAddr j).toNat = 0x80600+4*j.val := by
    unfold outputAddr
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hsource := sourceTableAddr_toNat s j.val table
  have hbase : (s.getReg .x17).toNat = 0xfff800 ∨
      (s.getReg .x17).toNat = 0xfffc00 := by
    rcases table with h | h <;> rw [h] <;> simp
  have hword_out := aligned4_getByte_word32 (copyLoop s 16) (outputAddr j) k
    (by rw [houtput]; omega) (by rw [houtput]; omega)
  have hword_source := aligned4_getByte_word32 s (sourceTableAddr s j.val) k
    (by rw [hsource]; omega) (by rw [hsource]; omega)
  have haddr : outputAddr j + BitVec.ofNat 64 k.val =
      BitVec.ofNat 64 (0x80600+4*j.val+k.val) := by
    simp only [outputAddr, ← BitVec.ofNat_add]
  rw [haddr] at hword_out
  rw [hword] at hword_out
  exact hword_out.trans hword_source.symm

#print axioms copyLoop_output_bytes

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteWordBridge67
