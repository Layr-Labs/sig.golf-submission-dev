import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Hash67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQueryWords67

/-! The upper signer H3 header and endpoint buffer encode the functional leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev prepared := GroupedBalancedSignUpperH3Header67.headerState

theorem header_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
    (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018) :
    (prepared s).getMem a = s.getMem a := by
  simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  split_ifs <;> simp_all

theorem header_head (s : MachineState) (base : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base) :
    (prepared s).getMem 0x80000 = KeygenDomain.header 3 base 0 0 0 := by
  have raw : (prepared s).getMem 0x80000 =
      (3 : Word) + (s.getMem 0x81000 <<< 8) := by
    simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  rw [raw,level,KeygenDomain.shift_ofNat]
  simp [KeygenDomain.header,BitVec.ofNat_add]

theorem header_index (s : MachineState) (leaf : Nat)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64) :
    ∀ j : Fin 3,
      (prepared s).getMem (Signing.wordAddress 0x80008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64 := by
  intro j
  fin_cases j
  · change (prepared s).getMem 0x80008 = _
    simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    simpa [Signing.wordAddress] using address 0
  · change (prepared s).getMem 0x80010 = _
    simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    simpa [Signing.wordAddress] using address 1
  · change (prepared s).getMem 0x80018 = _
    simp [prepared,GroupedBalancedSignUpperH3Header67.headerState,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    simpa [Signing.wordAddress] using address 2

theorem header_endpoint (s : MachineState) (j : Fin 134) :
    (prepared s).getMem (Signing.wordAddress 0x80020 j.val) =
      s.getMem (Signing.wordAddress 0x80020 j.val) := by
  have above : 0x80020 ≤ (Signing.wordAddress 0x80020 j.val).toNat := by
    simp [Signing.wordAddress,BitVec.toNat_ofNat]
    have := j.isLt
    omega
  apply header_frame s
  all_goals
    intro eq
    have high := above
    rw [eq] at high
    have low : (Signing.wordAddress 0x80020 j.val).toNat < 0x80020 := by
      rw [eq]
      all_goals decide
    omega

theorem header_input (s : MachineState) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (endpoints : ∀ j : Fin 134,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        (values ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
          (64*(j.val%2)) 64) :
    ∀ i : Fin 138,
      (prepared s).getMem (Signing.wordAddress 0x80000 i.val) =
        GroupedBalancedByteFastLeafQueryWords67.inputWord
          (KeygenDomain.header 3 base 0 0 0) leaf values i := by
  intro i
  by_cases first : i.val = 0
  · have eq : i = 0 := Fin.ext first
    subst i
    simpa [GroupedBalancedByteFastLeafQueryWords67.inputWord,
      Signing.wordAddress] using header_head s base level
  by_cases head : i.val < 4
  · have cases : i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
    rcases cases with h | h | h
    · have eq : i = 1 := Fin.ext h
      subst i
      simpa [GroupedBalancedByteFastLeafQueryWords67.inputWord,
        Signing.wordAddress] using header_index s leaf address 0
    · have eq : i = 2 := Fin.ext h
      subst i
      simpa [GroupedBalancedByteFastLeafQueryWords67.inputWord,
        Signing.wordAddress] using header_index s leaf address 1
    · have eq : i = 3 := Fin.ext h
      subst i
      simpa [GroupedBalancedByteFastLeafQueryWords67.inputWord,
        Signing.wordAddress] using header_index s leaf address 2
  · let j : Fin 134 := ⟨i.val-4,by have := i.isLt; omega⟩
    have addr : Signing.wordAddress 0x80000 i.val =
        Signing.wordAddress 0x80020 j.val := by
      simp [Signing.wordAddress,j]
      congr 1
      omega
    rw [addr,header_endpoint s j,endpoints j]
    simp only [GroupedBalancedByteFastLeafQueryWords67.inputWord,
      if_neg first,if_neg head,j]

theorem leaf_hash_eq (hash : Hash) (s : MachineState) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (endpoints : ∀ j : Fin 134,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        (values ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
          (64*(j.val%2)) 64) :
    Reference.truncate (hash (hashInput (prepared s))) =
      GroupedBalancedUpperTree67.compressLeaf hash base leaf values := by
  have regs := GroupedBalancedSignUpperH3Header67.header_regs s
  exact GroupedBalancedByteFastLeafQueryWords67.leaf_hash_eq hash
    (prepared s) base leaf values regs.2.1 regs.2.2.1
    (header_input s base leaf values level address endpoints)

#print axioms header_frame
#print axioms header_head
#print axioms header_index
#print axioms header_input
#print axioms leaf_hash_eq
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Query67
