import SigGolfCandidate.Hypertree.BalancedPatchWords
import SigGolfCandidate.Hypertree.BalancedPatchTails

/-! Inlined from SigGolfCandidate.Hypertree.BalancedPatchWordsSemantics; its only importer was SigGolfCandidate.Hypertree.BalancedPatchBodySemantics. -/
section
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
end

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

def flipBody (s : MachineState) : MachineState := tailPass (wordPass s)

private theorem digit_address_inj (i j : Nat) (hi : i < 43) (hj : j < 43)
    (eq : BitVec.ofNat 64 (0x80600+i) = BitVec.ofNat 64 (0x80600+j)) : i = j := by
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80600+i < 2^64),
    Nat.mod_eq_of_lt (by omega : 0x80600+j < 2^64)] at h
  omega

private theorem wordPass_tail_unchanged (s : MachineState) (t : Fin 3)
    (base : s.getReg .x15 = 0x80600) :
    (wordPass s).getByte (BitVec.ofNat 64 (0x80600+40+t.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600+40+t.val)) := by
  apply wordPass_frame s _ _ base
  intro j
  fin_cases t <;> fin_cases j <;> decide

theorem flipBody_byte (s : MachineState) (i : Fin 43)
    (base : s.getReg .x15 = 0x80600)
    (mask : s.getReg .x16 = 0x0707070707070707)
    (raw : ∀ i : Fin 43,
      (s.getByte (BitVec.ofNat 64 (0x80600+i.val))).toNat ≤ 7) :
    (flipBody s).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
      BitVec.ofNat 8 (7-(s.getByte (BitVec.ofNat 64 (0x80600+i.val))).toNat) := by
  have raw40 : ∀ j : Fin 5, ∀ k : Fin 8,
      (s.getByte (BitVec.ofNat 64 (0x80600+8*j.val+k.val))).toNat ≤ 7 := by
    intro j k
    let q : Fin 43 := ⟨8*j.val+k.val, by omega⟩
    simpa only [q, Fin.val_mk, Nat.add_assoc] using raw q
  by_cases first : i.val < 40
  · let j : Fin 5 := ⟨i.val/8, by omega⟩
    let k : Fin 8 := ⟨i.val%8, Nat.mod_lt _ (by decide)⟩
    have addr : BitVec.ofNat 64 (0x80600+i.val) =
        BitVec.ofNat 64 (0x80600+8*j.val+k.val) := by
      congr 1
      dsimp [j,k]
      omega
    have outside : ∀ t : Fin 3,
        BitVec.ofNat 64 (0x80600+i.val) ≠ BitVec.ofNat 64 (0x80600+40+t.val) := by
      intro t same
      have same' : BitVec.ofNat 64 (0x80600+i.val) =
          BitVec.ofNat 64 (0x80600+(40+t.val)) := by
        simpa only [Nat.add_assoc] using same
      have h := digit_address_inj i.val (40+t.val) i.isLt (by omega) same'
      omega
    have tail := tailPass_other (wordPass s) (BitVec.ofNat 64 (0x80600+i.val))
      ((wordPass_regs s).1.trans base) outside
    rw [flipBody, tail, addr]
    have digit := wordPass_byte s j k base mask raw40
    simpa only [← addr] using digit
  · let t : Fin 3 := ⟨i.val-40, by omega⟩
    have addr : BitVec.ofNat 64 (0x80600+i.val) =
        BitVec.ofNat 64 (0x80600+40+t.val) := by
      congr 1
      dsimp [t]
      omega
    have rawTail : ∀ u : Fin 3,
        ((wordPass s).getByte (BitVec.ofNat 64 (0x80600+40+u.val))).toNat ≤ 7 := by
      intro u
      rw [wordPass_tail_unchanged s u base]
      let q : Fin 43 := ⟨40+u.val, by omega⟩
      simpa only [q, Fin.val_mk, Nat.add_assoc] using raw q
    have digit := tailPass_digit (wordPass s) t ((wordPass_regs s).1.trans base) rawTail
    rw [flipBody, addr]
    rw [wordPass_tail_unchanged s t base] at digit
    exact digit

private theorem byte_outside_word (a : Word)
    (outside : ∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val))
    (j : Fin 5) :
    alignToDword a ≠ BitVec.ofNat 64 (0x80600+8*j.val) := by
  intro aligned
  let k : Fin 8 := ⟨byteOffset a, byteOffset_lt_8⟩
  let i : Fin 43 := ⟨8*j.val+k.val, by omega⟩
  have addr : a = BitVec.ofNat 64 (0x80600+i.val) := by
    calc
      a = alignToDword a + BitVec.ofNat 64 (byteOffset a) := (alignToDword_add_byteOffset a).symm
      _ = BitVec.ofNat 64 (0x80600+i.val) := by
        rw [aligned]
        simp only [i, k, ← BitVec.ofNat_add]
        congr 1
        omega
  exact outside i addr

theorem flipBody_frame (s : MachineState) (a : Word)
    (base : s.getReg .x15 = 0x80600)
    (outside : ∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val)) :
    (flipBody s).getByte a = s.getByte a := by
  have tailOutside : ∀ t : Fin 3, a ≠ BitVec.ofNat 64 (0x80600+40+t.val) := by
    intro t
    let i : Fin 43 := ⟨40+t.val, by omega⟩
    simpa only [i, Fin.val_mk, Nat.add_assoc] using outside i
  calc
    (flipBody s).getByte a = (wordPass s).getByte a :=
      tailPass_other (wordPass s) a ((wordPass_regs s).1.trans base) tailOutside
    _ = s.getByte a := wordPass_frame s a (byte_outside_word a outside) base

#print axioms flipBody_byte
#print axioms flipBody_frame
end SigGolfCandidate.Hypertree.Signing
