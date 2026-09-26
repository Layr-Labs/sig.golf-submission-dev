import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedReady67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Index67
import SigGolfCandidate.Hypertree.KeygenDomain


/-! Begin an upper leaf by resetting its 67-chain WOTS counter. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperStepZero67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def zeroState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x38)
  execInstrBr s (.SD .x28 .x6 0)

private theorem zero_code :
    Keygen.instructionAt image 0x18e8 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x18ec = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x18f0 = some (.base (.ADDI .x28 .x28 0x38)) ∧
    Keygen.instructionAt image 0x18f4 = some (.base (.SD .x28 .x6 0)) := by decide

theorem zero_steps (s : MachineState) (pc : s.pc = 0x18e8) :
    OrdinarySteps image s 4 (zeroState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0x38)
  obtain ⟨c0,c1,c2,c3⟩ := zero_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0x38)) 1
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 (zeroState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · have haddr : s3.getReg .x28 = 0x81038 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s3.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (zeroState s) else none) = some (zeroState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem zero_pc (s : MachineState) (pc : s.pc = 0x18e8) :
    (zeroState s).pc = 0x18f8 := by
  simp [zeroState,execInstrBr,pc]

theorem zero_step (s : MachineState) :
    (zeroState s).getMem 0x81038 = 0 := by
  simp [zeroState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem zero_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81038) :
    (zeroState s).getMem a = s.getMem a := by
  simp [zeroState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro eq
  exact False.elim (ha eq)


#print axioms zero_steps
#print axioms zero_pc
#print axioms zero_step
#print axioms zero_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperStepZero67


/-! Machine H2 address and value layout for the first chain step. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Layout67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def prepared (s : MachineState) : MachineState :=
  GroupedBalancedSignUpperH2Index67.indexState
    (GroupedBalancedSignUpperH2Header67.headerState
      (GroupedBalancedSignUpperStepZero67.zeroState s))

theorem prepared_steps (s : MachineState) (pc : s.pc = 0x18e8) :
    OrdinarySteps image s 41 (prepared s) := by
  let z := GroupedBalancedSignUpperStepZero67.zeroState s
  let h := GroupedBalancedSignUpperH2Header67.headerState z
  have ztrace := GroupedBalancedSignUpperStepZero67.zero_steps s pc
  have htrace := GroupedBalancedSignUpperH2Header67.header_steps z
    (GroupedBalancedSignUpperStepZero67.zero_pc s pc)
  have itrace := GroupedBalancedSignUpperH2Index67.index_steps h
    (GroupedBalancedSignUpperH2Header67.header_pc z
      (GroupedBalancedSignUpperStepZero67.zero_pc s pc))
  have first := Keygen.ordinary_trans image s z h 4 19 ztrace htrace
  have full := Keygen.ordinary_trans image s h (prepared s) 23 18
    (by simpa only [Nat.reduceAdd] using first) itrace
  simpa only [Nat.reduceAdd] using full

theorem prepared_pc (s : MachineState) (pc : s.pc = 0x18e8) :
    (prepared s).pc = 0x198c := by
  exact GroupedBalancedSignUpperH2Index67.index_pc _
    (GroupedBalancedSignUpperH2Header67.header_pc _
      (GroupedBalancedSignUpperStepZero67.zero_pc s pc))

theorem prepared_x19 (s : MachineState) :
    (prepared s).getReg .x19 = s.getReg .x19 := by
  simp [prepared,GroupedBalancedSignUpperH2Index67.indexState,
    GroupedBalancedSignUpperH2Header67.headerState,
    GroupedBalancedSignUpperStepZero67.zeroState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem prepared_stack (s : MachineState) :
    (prepared s).getReg .x2 = s.getReg .x2 := by
  simp [prepared,GroupedBalancedSignUpperH2Index67.indexState,
    GroupedBalancedSignUpperH2Header67.headerState,
    GroupedBalancedSignUpperStepZero67.zeroState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem prepared_high_frame (s : MachineState) (a : Word)
    (high : 0x80600 ≤ a.toNat) (counter : a ≠ 0x81038) :
    (prepared s).getMem a = s.getMem a := by
  have ne0 : a ≠ 0x80000 := by
    intro h; have he := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at he
    omega
  have ne1 : a ≠ 0x80008 := by
    intro h; have he := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at he
    omega
  have ne2 : a ≠ 0x80010 := by
    intro h; have he := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at he
    omega
  have ne3 : a ≠ 0x80018 := by
    intro h; have he := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat] at he
    omega
  change (GroupedBalancedSignUpperH2Index67.indexState
    (GroupedBalancedSignUpperH2Header67.headerState
      (GroupedBalancedSignUpperStepZero67.zeroState s))).getMem a = _
  rw [GroupedBalancedSignUpperH2Index67.index_frame _ a ne1 ne2 ne3,
    GroupedBalancedSignUpperH2Header67.header_frame _ a ne0,
    GroupedBalancedSignUpperStepZero67.zero_frame s a counter]

theorem prepared_low_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (prepared s).getMem a = s.getMem a := by
  have ne (n : Nat) (hn : 0x80000 ≤ n) (hb : n < 2^64) :
      a ≠ BitVec.ofNat 64 n := by
    intro eq
    have h := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] at h
    omega
  change (GroupedBalancedSignUpperH2Index67.indexState
    (GroupedBalancedSignUpperH2Header67.headerState
      (GroupedBalancedSignUpperStepZero67.zeroState s))).getMem a = _
  rw [GroupedBalancedSignUpperH2Index67.index_frame _ a
      (ne 0x80008 (by decide) (by decide))
      (ne 0x80010 (by decide) (by decide))
      (ne 0x80018 (by decide) (by decide)),
    GroupedBalancedSignUpperH2Header67.header_frame _ a
      (ne 0x80000 (by decide) (by decide)),
    GroupedBalancedSignUpperStepZero67.zero_frame s a
      (ne 0x81038 (by decide) (by decide))]

theorem prepared_key_frame (s : MachineState) (j : Fin 4) :
    (prepared s).getMem (Signing.wordAddress 0x20 j.val) =
      s.getMem (Signing.wordAddress 0x20 j.val) := by
  let a := Signing.wordAddress 0x20 j.val
  change (GroupedBalancedSignUpperH2Index67.indexState
    (GroupedBalancedSignUpperH2Header67.headerState
      (GroupedBalancedSignUpperStepZero67.zeroState s))).getMem a = _
  rw [GroupedBalancedSignUpperH2Index67.index_frame _ a
      (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      (by fin_cases j <;> decide),
    GroupedBalancedSignUpperH2Header67.header_frame _ a
      (by fin_cases j <;> decide),
    GroupedBalancedSignUpperStepZero67.zero_frame s a
      (by fin_cases j <;> decide)]

private theorem header_math (base chain step : Nat) :
    (2 : Word) + (BitVec.ofNat 64 base <<< 8) +
      (BitVec.ofNat 64 chain <<< 24) +
      (BitVec.ofNat 64 step <<< 32) =
      KeygenDomain.header 2 base 0 chain step := by
  unfold KeygenDomain.header
  rw [Nat.zero_mul, Nat.add_zero]
  rw [KeygenDomain.shift_ofNat, KeygenDomain.shift_ofNat,
    KeygenDomain.shift_ofNat]
  conv_rhs => rw [BitVec.ofNat_add]
  conv_rhs => rw [BitVec.ofNat_add]
  conv_rhs => rw [BitVec.ofNat_add]
  rfl

theorem prepared_header (s : MachineState) (base chain : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (chainWord : s.getMem 0x81030 = BitVec.ofNat 64 chain) :
    (prepared s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain 0 := by
  let z := GroupedBalancedSignUpperStepZero67.zeroState s
  let h := GroupedBalancedSignUpperH2Header67.headerState z
  have head := GroupedBalancedSignUpperH2Header67.header_word z
  have zl := GroupedBalancedSignUpperStepZero67.zero_frame s 0x81000 (by decide)
  have zc := GroupedBalancedSignUpperStepZero67.zero_frame s 0x81030 (by decide)
  rw [zl,zc,level,chainWord,
    GroupedBalancedSignUpperStepZero67.zero_step] at head
  have ih := GroupedBalancedSignUpperH2Index67.index_frame h 0x80000
    (by decide) (by decide) (by decide)
  change (GroupedBalancedSignUpperH2Index67.indexState h).getMem 0x80000 = _
  rw [ih,head]
  simpa using header_math base chain 0

theorem prepared_index (s : MachineState) (leaf : Nat)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64) :
    ∀ j : Fin 3,
      (prepared s).getMem (Signing.wordAddress 0x80008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64 := by
  intro j
  let z := GroupedBalancedSignUpperStepZero67.zeroState s
  let h := GroupedBalancedSignUpperH2Header67.headerState z
  have iw := GroupedBalancedSignUpperH2Index67.index_words h j
  have hf := GroupedBalancedSignUpperH2Header67.header_frame z
    (Signing.wordAddress 0x81008 j.val) (by fin_cases j <;> decide)
  have zf := GroupedBalancedSignUpperStepZero67.zero_frame s
    (Signing.wordAddress 0x81008 j.val) (by fin_cases j <;> decide)
  change (GroupedBalancedSignUpperH2Index67.indexState h).getMem _ = _
  rw [iw,hf,zf]
  exact address j

theorem prepared_value (s : MachineState) (value : Reference.Digest)
    (valueWords : ∀ j : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        value.extractLsb' (64*j.val) 64) :
    ∀ j : Fin 2,
      (prepared s).getMem (Signing.wordAddress 0x80020 j.val) =
        value.extractLsb' (64*j.val) 64 := by
  intro j
  let z := GroupedBalancedSignUpperStepZero67.zeroState s
  let h := GroupedBalancedSignUpperH2Header67.headerState z
  change (GroupedBalancedSignUpperH2Index67.indexState h).getMem _ = _
  rw [GroupedBalancedSignUpperH2Index67.index_frame h _
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide)]
  rw [GroupedBalancedSignUpperH2Header67.header_frame z _
    (by fin_cases j <;> decide)]
  rw [GroupedBalancedSignUpperStepZero67.zero_frame s _
    (by fin_cases j <;> decide)]
  exact valueWords j

theorem prepared_query (s : MachineState) (base leaf chain : Nat)
    (value : Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (chainWord : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (valueWords : ∀ j : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        value.extractLsb' (64*j.val) 64)
    (source : (prepared s).getReg .x10 = 0x80000)
    (bits : (prepared s).getReg .x11 = 384) :
    hashInput (prepared s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 base 0 chain 0) leaf value) := by
  apply KeygenDomain.query_eq (prepared s) _ leaf value source bits
  exact KeygenDomain.words_of_layout (prepared s)
    (KeygenDomain.header 2 base 0 chain 0) leaf value
    (prepared_header s base chain level chainWord)
    (prepared_index s leaf address)
    (prepared_value s value valueWords)

#print axioms prepared_steps
#print axioms prepared_x19
#print axioms prepared_query
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Layout67
