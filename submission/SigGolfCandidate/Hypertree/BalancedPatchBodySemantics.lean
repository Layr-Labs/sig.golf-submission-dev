import SigGolfCandidate.Hypertree.BalancedPatchWordsSemantics
import SigGolfCandidate.Hypertree.BalancedPatchTails

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
