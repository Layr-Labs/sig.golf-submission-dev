import SigGolfCandidate.Hypertree.BalancedPatchWords

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

private def wordPassPrefix (s : MachineState) : Nat → MachineState
  | 0 => s
  | n + 1 => flipChunk (wordPassPrefix s n) (BitVec.ofNat 12 (8*n))

private theorem wordPassPrefix_five (s : MachineState) : wordPassPrefix s 5 = wordPass s := by
  rfl

private theorem wordPassPrefix_base (s : MachineState) (n : Nat) :
    (wordPassPrefix s n).getReg .x15 = s.getReg .x15 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (flipChunk_regs (wordPassPrefix s n) _).1.trans ih

private theorem wordPassPrefix_mask (s : MachineState) (n : Nat) :
    (wordPassPrefix s n).getReg .x16 = s.getReg .x16 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (flipChunk_regs (wordPassPrefix s n) _).2.1.trans ih

private theorem chunk_word_ne (j k : Fin 5) (ne : j ≠ k) :
    BitVec.ofNat 64 (0x80600+8*j.val) ≠ BitVec.ofNat 64 (0x80600+8*k.val) := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := j.isLt; omega : 0x80600+8*j.val < 2^64),
    Nat.mod_eq_of_lt (by have := k.isLt; omega : 0x80600+8*k.val < 2^64)] at h
  exact ne (Fin.ext (by omega))

private theorem flipChunk_other (s : MachineState) (j k : Fin 5) (i : Fin 8)
    (base : s.getReg .x15 = 0x80600) (ne : j ≠ k) :
    (flipChunk s (BitVec.ofNat 12 (8*k.val))).getByte
        (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) := by
  apply flipChunk_byte_outside s k _ base
  have address : alignToDword (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      BitVec.ofNat 64 (0x80600+8*j.val) := by
    calc
      _ = s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (8*j.val)) :=
        chunk_address s j i base
      _ = _ := (chunk_word s j base).symm
  rw [address]
  exact chunk_word_ne j k ne

private theorem wordPassPrefix_unprocessed (s : MachineState) (n : Nat)
    (limit : n ≤ 5) (j : Fin 5) (i : Fin 8)
    (later : n ≤ j.val) (base : s.getReg .x15 = 0x80600) :
    (wordPassPrefix s n).getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let k : Fin 5 := ⟨n, by omega⟩
    have ne : j ≠ k := by
      intro eq
      have h := congrArg Fin.val eq
      change j.val = n at h
      omega
    change (flipChunk (wordPassPrefix s n) (BitVec.ofNat 12 (8*k.val))).getByte _ = _
    rw [flipChunk_other (wordPassPrefix s n) j k i
      (by rw [wordPassPrefix_base s n, base]) ne]
    exact ih (by omega) (by omega)

private theorem wordPassPrefix_processed (s : MachineState) (n : Nat)
    (limit : n ≤ 5) (j : Fin 5) (i : Fin 8) (earlier : j.val < n)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (raw : ∀ j : Fin 5, ∀ i : Fin 8,
      (s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val))).toNat ≤ 7) :
    (wordPassPrefix s n).getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val))).toNat) := by
  induction n with
  | zero => omega
  | succ n ih =>
    let k : Fin 5 := ⟨n, by omega⟩
    by_cases same : j = k
    ·
      have rawBefore : ∀ t : Fin 8,
          ((wordPassPrefix s n).getByte
            (BitVec.ofNat 64 (0x80600+8*k.val+t.val))).toNat ≤ 7 := by
        intro t
        rw [wordPassPrefix_unprocessed s n (by omega) k t (by simp [k]) base]
        exact raw k t
      have step := flipChunk_byte (wordPassPrefix s n) k i
        (by rw [wordPassPrefix_base s n, base])
        (by rw [wordPassPrefix_mask s n, mask]) rawBefore
      rw [wordPassPrefix_unprocessed s n (by omega) k i (by simp [k]) base] at step
      change (flipChunk (wordPassPrefix s n) (BitVec.ofNat 12 (8*k.val))).getByte _ = _
      simpa only [same] using step
    · have step := flipChunk_other (wordPassPrefix s n) j k i
        (by rw [wordPassPrefix_base s n, base]) same
      change (flipChunk (wordPassPrefix s n) (BitVec.ofNat 12 (8*k.val))).getByte _ = _
      rw [step]
      exact ih (by omega) (by
        have h : j.val ≠ n := by
          intro eq
          exact same (Fin.ext (by simpa [k] using eq))
        omega)

/-- The five packed updates complement exactly the first forty digit bytes. -/
theorem wordPass_byte (s : MachineState) (j : Fin 5) (i : Fin 8)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (raw : ∀ j : Fin 5, ∀ i : Fin 8,
      (s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val))).toNat ≤ 7) :
    (wordPass s).getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+i.val))).toNat) := by
  rw [← wordPassPrefix_five]
  exact wordPassPrefix_processed s 5 (by omega) j i (by omega) base mask raw

private theorem wordPassPrefix_frame (s : MachineState) (n : Nat)
    (limit : n ≤ 5) (a : Word)
    (outside : ∀ j : Fin 5,
      alignToDword a ≠ BitVec.ofNat 64 (0x80600+8*j.val))
    (base : s.getReg .x15 = 0x80600) :
    (wordPassPrefix s n).getByte a = s.getByte a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let k : Fin 5 := ⟨n, by omega⟩
    change (flipChunk (wordPassPrefix s n) (BitVec.ofNat 12 (8*k.val))).getByte a = _
    rw [flipChunk_byte_outside (wordPassPrefix s n) k a
      (by rw [wordPassPrefix_base s n, base]) (outside k)]
    exact ih (by omega)

/-- All bytes outside the first forty digit bytes retain their old value. -/
theorem wordPass_frame (s : MachineState) (a : Word)
    (outside : ∀ j : Fin 5,
      alignToDword a ≠ BitVec.ofNat 64 (0x80600+8*j.val))
    (base : s.getReg .x15 = 0x80600) :
    (wordPass s).getByte a = s.getByte a := by
  rw [← wordPassPrefix_five]
  exact wordPassPrefix_frame s 5 (by omega) a outside base

#print axioms wordPass_byte
#print axioms wordPass_frame

end SigGolfCandidate.Hypertree.Signing
