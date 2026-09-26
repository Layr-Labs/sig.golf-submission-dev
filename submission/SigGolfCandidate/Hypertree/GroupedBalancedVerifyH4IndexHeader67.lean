import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHeader67

/-! The verifier's three scratch words encode a 192-bit tree index. Its H4
round header shifts that index right by one bit. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def StoredIndex (s : MachineState) (index : BitVec 192) : Prop :=
  ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      index.extractLsb' (64 * i.val) 64

private theorem shifted_limb (index : BitVec 192) (i : Fin 2) :
    (index.extractLsb' (64 * i.val) 64 >>> 1) +
      (index.extractLsb' (64 * (i.val + 1)) 64 <<< 63) =
      (index >>> 1).extractLsb' (64 * i.val) 64 := by
  apply BitVec.eq_of_toNat_eq
  fin_cases i <;>
    simp [BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_shiftLeft, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] <;> omega

private theorem shifted_high_limb (index : BitVec 192) :
    (index.extractLsb' 128 64 >>> 1) =
      (index >>> 1).extractLsb' 128 64 := by
  apply BitVec.eq_of_toNat_eq
  have bound := index.isLt
  simp [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem header_mem (s : MachineState) (a : Word) :
    (GroupedBalancedVerifyTreeHeader67.headerState s).getMem a =
      if a = 0x81018 then s.getMem 0x81018 >>> 1 else
      if a = 0x81010 then
        (s.getMem 0x81010 >>> 1) + (s.getMem 0x81018 <<< 63) else
      if a = 0x81008 then
        (s.getMem 0x81008 >>> 1) + (s.getMem 0x81010 <<< 63) else
      if a = 0x81020 then s.getMem 0x81008 &&& 1 else s.getMem a := by
  simp [GroupedBalancedVerifyTreeHeader67.headerState, execInstrBr,
    signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem header_refines (s : MachineState) (index : BitVec 192)
    (stored : StoredIndex s index) :
    StoredIndex (GroupedBalancedVerifyTreeHeader67.headerState s)
      (index >>> 1) := by
  have w0 : s.getMem 0x81008 = index.extractLsb' 0 64 := stored 0
  have w1 : s.getMem 0x81010 = index.extractLsb' 64 64 := stored 1
  have w2 : s.getMem 0x81018 = index.extractLsb' 128 64 := stored 2
  intro i
  fin_cases i
  · change (GroupedBalancedVerifyTreeHeader67.headerState s).getMem 0x81008 = _
    rw [header_mem, if_neg (by decide), if_neg (by decide), if_pos rfl, w0, w1]
    exact shifted_limb index 0
  · change (GroupedBalancedVerifyTreeHeader67.headerState s).getMem 0x81010 = _
    rw [header_mem, if_neg (by decide), if_pos rfl, w1, w2]
    exact shifted_limb index 1
  · change (GroupedBalancedVerifyTreeHeader67.headerState s).getMem 0x81018 = _
    rw [header_mem, if_pos rfl, w2]
    exact shifted_high_limb index

#print axioms header_refines
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexHeader67
