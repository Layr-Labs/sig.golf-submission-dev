import SigGolfCandidate.Hypertree.BalancedPatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion

private theorem extractByte_eq_slice (w : Word) (i : Nat) :
    extractByte w i = w.extractLsb' (8*i) 8 := by
  simp only [extractByte, BitVec.extractLsb', Nat.mul_comm i 8]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

/-- Exact byte action of a packed 8-byte flip, with the address already decomposed. -/
theorem flipChunk_byte_at (s : MachineState) (off : BitVec 12) (a : Word)
    (i : Fin 8)
    (ha : alignToDword a = s.getReg .x15 + signExtend12 off)
    (hi : byteOffset a = i.val)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (raw : ∀ k : Fin 8,
      ((s.getMem (s.getReg .x15 + signExtend12 off)).extractLsb' (8*k.val) 8).toNat ≤ 7) :
    (flipChunk s off).getByte a = BitVec.ofNat 8 (7-(s.getByte a).toNat) := by
  let w := s.getMem (s.getReg .x15 + signExtend12 off)
  have hv := BalancedPacked.flip_word_byte w raw i
  change extractByte ((flipChunk s off).getMem (alignToDword a)) (byteOffset a) = _
  rw [ha, hi, flipChunk_mem, if_pos rfl, mask]
  have old : s.getByte a = w.extractLsb' (8*i.val) 8 := by
    simp only [MachineState.getByte, ha, hi, extractByte_eq_slice]
    rfl
  rw [old]
  rw [extractByte_eq_slice]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have hlt : 7 - (w.extractLsb' (8 * i.val) 8).toNat < 2^8 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  exact hv

/-- All other aligned words retain their byte view. -/
theorem flipChunk_byte_frame (s : MachineState) (off : BitVec 12) (a : Word)
    (outside : alignToDword a ≠ s.getReg .x15 + signExtend12 off) :
    (flipChunk s off).getByte a = s.getByte a := by
  simp only [MachineState.getByte, flipChunk_mem, if_neg outside]


theorem chunk_word (s : MachineState) (j : Fin 5)
    (base : s.getReg .x15 = 0x80600) :
    BitVec.ofNat 64 (0x80600+8*j.val) =
      s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (8*j.val)) := by
  rw [base]
  fin_cases j <;> decide

theorem chunk_address (s : MachineState) (j : Fin 5) (i : Fin 8)
    (base : s.getReg .x15 = 0x80600) :
    alignToDword (BitVec.ofNat 64 (0x80600 + 8*j.val + i.val)) =
      s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (8*j.val)) := by
  have hsmall : 0x80600 + 8*j.val + i.val < 2^64 := by omega
  have halign : (BitVec.ofNat 64 (0x80600+8*j.val)).toNat % 8 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x80600+8*j.val < 2^64)]
    omega
  have hover : (BitVec.ofNat 64 (0x80600+8*j.val)).toNat + i.val < 2^64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x80600+8*j.val < 2^64)]
    omega
  rw [show BitVec.ofNat 64 (0x80600+8*j.val+i.val) =
      BitVec.ofNat 64 (0x80600+8*j.val) + BitVec.ofNat 64 i.val by
        rw [← BitVec.ofNat_add]]
  rw [alignToDword_add_ofNat_of_aligned halign hover]
  have div : i.val / 8 = 0 := by omega
  rw [div]
  simpa using chunk_word s j base

theorem chunk_offset (j : Fin 5) (i : Fin 8) :
    byteOffset (BitVec.ofNat 64 (0x80600 + 8*j.val + i.val)) = i.val := by
  have halign : (BitVec.ofNat 64 (0x80600+8*j.val)).toNat % 8 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x80600+8*j.val < 2^64)]
    omega
  have hover : (BitVec.ofNat 64 (0x80600+8*j.val)).toNat + i.val < 2^64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x80600+8*j.val < 2^64)]
    omega
  rw [show BitVec.ofNat 64 (0x80600+8*j.val+i.val) =
      BitVec.ofNat 64 (0x80600+8*j.val) + BitVec.ofNat 64 i.val by
        rw [← BitVec.ofNat_add]]
  rw [byteOffset_add_ofNat_of_aligned halign hover]
  exact Nat.mod_eq_of_lt i.isLt

/-- Bytewise complement for any of the five aligned eight-byte chunks. -/
theorem flipChunk_byte (s : MachineState) (j : Fin 5) (i : Fin 8)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (raw : ∀ k : Fin 8,
      (s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+k.val))).toNat ≤ 7) :
    (flipChunk s (BitVec.ofNat 12 (8*j.val))).getByte
        (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val))).toNat) := by
  apply flipChunk_byte_at s _ _ i (chunk_address s j i base) (chunk_offset j i) mask
  intro k
  have h := raw k
  have old := getByte_word s (0x80600+8*j.val) k.val (by omega) (by omega)
  have div : k.val/8=0 := by omega
  have mod : k.val%8=k.val := Nat.mod_eq_of_lt k.isLt
  rw [div, mod] at old
  have word : wordAddress (0x80600+8*j.val) 0 =
      s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (8*j.val)) := by
    simpa [wordAddress] using chunk_word s j base
  rw [word, extractByte_eq_slice] at old
  rw [old] at h
  exact h

/-- Every byte in a different aligned word is unchanged by the selected chunk. -/
theorem flipChunk_byte_outside (s : MachineState) (j : Fin 5) (a : Word)
    (base : s.getReg .x15 = 0x80600)
    (outside : alignToDword a ≠ BitVec.ofNat 64 (0x80600+8*j.val)) :
    (flipChunk s (BitVec.ofNat 12 (8*j.val))).getByte a = s.getByte a := by
  apply flipChunk_byte_frame
  have addr := chunk_word s j base
  rw [← addr]
  exact outside 

#print axioms flipChunk_byte_at
#print axioms flipChunk_byte_frame
#print axioms flipChunk_byte
#print axioms flipChunk_byte_outside
end SigGolfCandidate.Hypertree.Signing
