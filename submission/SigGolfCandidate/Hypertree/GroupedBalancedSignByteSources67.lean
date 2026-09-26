import SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteSources67

theorem align_add_offset_toNat (addr : Word) :
    (alignToDword addr).toNat + byteOffset addr = addr.toNat := by
  unfold alignToDword byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
             show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hlo : addr.toNat &&& 7 = addr.toNat % 8 := by
    have h := Nat.and_two_pow_sub_one_eq_mod addr.toNat 3
    simpa using h
  have hhi_mod : (addr.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
        show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (addr.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = addr.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
        show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := addr.isLt; omega)
  have hhi : addr.toNat &&& (2 ^ 64 - 1 - 7) = addr.toNat / 8 * 8 := by
    have heucl := Nat.div_add_mod (addr.toNat &&& (2 ^ 64 - 1 - 7)) 8
    omega
  rw [hlo, hhi]
  omega

theorem align_ne_of_gap (a b : Word)
    (gap : a.toNat + 7 < b.toNat ∨ b.toNat + 7 < a.toNat) :
    alignToDword a ≠ alignToDword b := by
  intro h
  have ha := align_add_offset_toNat a
  have hb := align_add_offset_toNat b
  have hval := congrArg BitVec.toNat h
  have hba := byteOffset_lt_8 (addr := a)
  have hbb := byteOffset_lt_8 (addr := b)
  omega

def tableAddr (s : MachineState) : Word :=
  s.getReg .x17 + (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2)

theorem tableAddr_lower (s : MachineState)
    (hbase : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00) :
    0xfff800 ≤ (tableAddr s).toNat := by
  unfold tableAddr
  rcases hbase with h | h <;> rw [h] <;>
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  · have hv := (s.getByte (s.getReg .x10)).isLt
    simp only [show (0xfff800 : Word).toNat = 0xfff800 by decide,
      show (s.getByte (s.getReg .x10)).toNat % 2 ^ 64 =
        (s.getByte (s.getReg .x10)).toNat from Nat.mod_eq_of_lt (by omega)]
    omega
  · have hv := (s.getByte (s.getReg .x10)).isLt
    simp only [show (0xfffc00 : Word).toNat = 0xfffc00 by decide,
      show (s.getByte (s.getReg .x10)).toNat % 2 ^ 64 =
        (s.getByte (s.getReg .x10)).toNat from Nat.mod_eq_of_lt (by omega)]
    omega

theorem copy_input_output_disjoint (s : MachineState) (i j : Nat)
    (hi : i < 16) (hj : j < 16)
    (hinput : s.getReg .x10 = BitVec.ofNat 64 (0x80500 + i))
    (houtput : s.getReg .x11 = BitVec.ofNat 64 (0x80600 + 4*j)) :
    alignToDword (s.getReg .x10) ≠ alignToDword (s.getReg .x11) := by
  apply align_ne_of_gap
  left
  rw [hinput,houtput]
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80500 + i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 0x80600 + 4*j < 2 ^ 64)]
  omega

theorem copy_table_output_disjoint (s : MachineState) (j : Nat)
    (hj : j < 16)
    (htable : s.getReg .x17 = 0xfff800 ∨ s.getReg .x17 = 0xfffc00)
    (houtput : s.getReg .x11 = BitVec.ofNat 64 (0x80600 + 4*j)) :
    alignToDword (tableAddr s) ≠ alignToDword (s.getReg .x11) := by
  apply align_ne_of_gap
  right
  have ht := tableAddr_lower s htable
  rw [houtput]
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80600 + 4*j < 2 ^ 64)]
  omega

def sourceAddress (a : Word) : Prop :=
  a.toNat < 0x80510 ∨ 0xfff800 ≤ a.toNat

theorem source_output_disjoint (s : MachineState) (j : Nat) (hj : j < 16)
    (houtput : s.getReg .x11 = BitVec.ofNat 64 (0x80600 + 4*j))
    (a : Word) (hsource : sourceAddress a) :
    alignToDword a ≠ alignToDword (s.getReg .x11) := by
  apply align_ne_of_gap
  rw [houtput]
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80600 + 4*j < 2 ^ 64)]
  rcases hsource with hlow | hhigh
  · left; omega
  · right; omega

theorem copyLoop_preserves_source_byte (s : MachineState)
    (output : s.getReg .x11 = 0x80600) (n : Nat) (hn : n ≤ 16)
    (a : Word) (hsource : sourceAddress a) :
    (copyLoop s n).getByte a = s.getByte a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have houtput : (copyLoop s n).getReg .x11 =
        BitVec.ofNat 64 (0x80600+4*n) := by
      rw [copyLoop_output_pointer, output, BitVec.ofNat_add]
      rfl
    have hd := source_output_disjoint (copyLoop s n) n hn1 houtput a hsource
    change (copyBody (copyLoop s n)).getByte a = s.getByte a
    rw [copyBody_preserves_byte _ _ hd]
    exact ih hn0

theorem copyLoop_preserves_source_word (s : MachineState)
    (output : s.getReg .x11 = 0x80600) (n : Nat) (hn : n ≤ 16)
    (a : Word) (hsource : sourceAddress a) :
    (copyLoop s n).getWord32 a = s.getWord32 a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have houtput : (copyLoop s n).getReg .x11 =
        BitVec.ofNat 64 (0x80600+4*n) := by
      rw [copyLoop_output_pointer, output, BitVec.ofNat_add]
      rfl
    have hd := source_output_disjoint (copyLoop s n) n hn1 houtput a hsource
    rw [copyLoop, copyBody_preserves_word _ _ (Or.inl hd)]
    exact ih hn0

#print axioms copyLoop_preserves_source_byte
#print axioms copyLoop_preserves_source_word

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteSources67
