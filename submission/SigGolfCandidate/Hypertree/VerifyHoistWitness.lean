import SigGolfCandidate.Hypertree.VerifyHoistLoop

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def chainSource (s : MachineState) : Word := s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)

def chainValueState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x430)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x448)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SLLI .x10 .x6 4)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x28)
  execInstrBr s (.SD .x28 .x11 0)

theorem chainValueState_block (s : MachineState) (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSource s) 8 = true) (valid8 : accessValid (chainSource s + 8) 8 = true) :
    OrdinarySteps verify s 16 (chainValueState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x430)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x448)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.SLLI .x10 .x6 4)
  let s8 := execInstrBr s7 (.ADD .x7 .x7 .x10)
  let s9 := execInstrBr s8 (.LD .x10 .x7 0)
  let s10 := execInstrBr s9 (.LD .x11 .x7 8)
  let s11 := execInstrBr s10 (.LUI .x28 0x80)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x20)
  let s13 := execInstrBr s12 (.SD .x28 .x10 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 0x28)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 15
  · have hp : s.pc = 0x1490 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x430)) 14
  · have hp : s1.pc = 0x1494 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 13
  · have hp : s2.pc = 0x1498 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s3.pc = 0x149c := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x448)) 11
  · have hp : s4.pc = 0x14a0 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 10
  · have hp : s5.pc = 0x14a4 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.SLLI .x10 .x6 4)) 9
  · have hp : s6.pc = 0x14a8 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x7 .x7 .x10)) 8
  · have hp : s7.pc = 0x14ac := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x10 .x7 0)) 7
  · have hp : s8.pc = 0x14b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chainSource] using valid0
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x11 .x7 8)) 6
  · have hp : s9.pc = 0x14b4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chainSource] using valid8
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x80)) 5
  · have hp : s10.pc = 0x14b8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x20)) 4
  · have hp : s11.pc = 0x14bc := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x10 0)) 3
  · have hp : s12.pc = 0x14c0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s13.pc = 0x14c4 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 0x28)) 1
  · have hp : s14.pc = 0x14c8 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s15.pc = 0x14cc := by simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem chainValueState_mem (s : MachineState) (a : Word) :
    (chainValueState s).getMem a = if a = 0x80028 then s.getMem (chainSource s + 8) else
      if a = 0x80020 then s.getMem (chainSource s) else s.getMem a := by
  simp [chainValueState, chainSource, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_chain (s : MachineState) :
    (chainValueState s).getReg .x6 = s.getMem 0x80430 := by
  simp [chainValueState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_pc (s : MachineState) : (chainValueState s).pc = s.pc + 64 := by
  simp [chainValueState, execInstrBr, BitVec.add_assoc]

theorem chainValueState_stack (s : MachineState) :
    (chainValueState s).getReg .x1 = s.getReg .x1 ∧ (chainValueState s).getReg .x2 = s.getReg .x2 := by
  simp [chainValueState, execInstrBr, MachineState.getReg_setReg_ne]

def digitState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x600)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LBU .x10 .x7 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  execInstrBr s (.ADDI .x28 .x28 0x438)

theorem digit_block (s : MachineState) (pc : s.pc = 0x14d0)
    (valid : accessValid (0x80600 + s.getReg .x6) 1 = true) :
    OrdinarySteps verify s 6 (digitState s) := by
  let s1 := execInstrBr s (.LUI .x7 0x80)
  let s2 := execInstrBr s1 (.ADDI .x7 .x7 0x600)
  let s3 := execInstrBr s2 (.ADD .x7 .x7 .x6)
  let s4 := execInstrBr s3 (.LBU .x10 .x7 0)
  let s5 := execInstrBr s4 (.LUI .x28 0x80)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x438)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x7 0x80)) 5
  · have hp : s.pc = 0x14d0 := pc
    simp only [fetch,hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x7 .x7 0x600)) 4
  · have hp : s1.pc = 0x14d4 := by simp [s1,execInstrBr,pc]
    simp only [fetch,hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x7 .x7 .x6)) 3
  · have hp : s2.pc = 0x14d8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simp only [fetch,hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LBU .x10 .x7 0)) 2
  · have hp : s3.pc = 0x14dc := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simp only [fetch,hp]; decide
  · simpa [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using valid
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x80)) 1
  · have hp : s4.pc = 0x14e0 := by simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simp only [fetch,hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x438)) 0
  · have hp : s5.pc = 0x14e4 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,BitVec.add_assoc]
    simp only [fetch,hp]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem digit_mem (s : MachineState) (a : Word) :
    (digitState s).getMem a = s.getMem a := by
  simp [digitState,execInstrBr]

theorem digit_pc (s : MachineState) : (digitState s).pc = s.pc + 24 := by
  simp [digitState,execInstrBr,BitVec.add_assoc]

theorem digit_regs (s : MachineState) :
    (digitState s).getReg .x10 = (s.getByte (0x80600 + s.getReg .x6)).zeroExtend 64 ∧
    (digitState s).getReg .x6 = s.getReg .x6 ∧
    (digitState s).getReg .x28 = 0x80438 ∧
    (digitState s).getReg .x1 = s.getReg .x1 ∧
    (digitState s).getReg .x2 = s.getReg .x2 := by
  simp [digitState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem chainValueState_digit (s : MachineState) (chain : Reference.Chain) :
    (chainValueState s).getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) := by
  rw [getByte_word _ 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
    getByte_word s 0x80600 chain.val (by decide) (by have := chain.isLt; omega),
    chainValueState_mem]
  rw [if_neg (by fin_cases chain <;> decide), if_neg (by fin_cases chain <;> decide)]

theorem chainValueState_sticky (s : MachineState) :
    (chainValueState s).getReg .x5 = s.getReg .x5 ∧
    (chainValueState s).getReg .x12 = s.getReg .x12 ∧
    (chainValueState s).getReg .x31 = s.getReg .x31 := by
  simp [chainValueState,execInstrBr,MachineState.getReg_setReg_ne]

theorem digit_sticky (s : MachineState) :
    (digitState s).getReg .x5 = s.getReg .x5 ∧
    (digitState s).getReg .x12 = s.getReg .x12 ∧
    (digitState s).getReg .x31 = s.getReg .x31 := by
  simp [digitState,execInstrBr,MachineState.getReg_setReg_ne]

theorem witness_prepare (s : MachineState) (level tree : Nat) (side : Bool)
    (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSource s) 8 = true)
    (valid8 : accessValid (chainSource s + 8) 8 = true)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (value0 : s.getMem (chainSource s) = value.extractLsb' 0 64)
    (value8 : s.getMem (chainSource s + 8) = value.extractLsb' 64 64)
    (digitEq : s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
      BitVec.ofNat 8 digit.val) :
    ∃ ready, OrdinarySteps verify s 22 ready ∧ ready.pc = 0x14e8 ∧
      ready.getReg .x10 = BitVec.ofNat 64 digit.val ∧
      ready.getReg .x6 = BitVec.ofNat 64 chain.val ∧
      ready.getReg .x28 = 0x80438 ∧
      ready.getMem 0x80400 = BitVec.ofNat 64 level ∧
      ready.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) ∧
      ready.getMem 0x80430 = BitVec.ofNat 64 chain.val ∧
      (∀ i : Fin 3, ready.getMem (wordAddress 0x80408 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2, ready.getMem (wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) ∧
      ready.getReg .x5 = s.getReg .x5 ∧
      ready.getReg .x12 = s.getReg .x12 ∧
      ready.getReg .x31 = s.getReg .x31 ∧
      ready.getReg .x1 = s.getReg .x1 ∧
      ready.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80020 → a ≠ 0x80028 → ready.getMem a = s.getMem a) := by
  let copied := chainValueState s
  have copiedPC : copied.pc = 0x14d0 := by rw [chainValueState_pc,pc]; rfl
  have addr : (0x80600 : Word) + BitVec.ofNat 64 chain.val =
      BitVec.ofNat 64 (0x80600 + chain.val) := (BitVec.ofNat_add _ _).symm
  have validDigit : accessValid (0x80600 + copied.getReg .x6) 1 = true := by
    rw [chainValueState_chain,chainEq,addr]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,MEMORY_BYTES,
      Nat.mod_one,decide_true,Bool.and_true,decide_eq_true_eq]
    have := chain.isLt
    omega
  have keep (a : Word) (low : a ≠ 0x80020) (high : a ≠ 0x80028) :
      (digitState copied).getMem a = s.getMem a := by
    rw [digit_mem,chainValueState_mem,if_neg high,if_neg low]
  let ready := digitState copied
  have reg := digit_regs copied
  have sticky0 := chainValueState_sticky s
  have sticky1 := digit_sticky copied
  refine ⟨ready,ordinary_trans verify s copied ready 16 6
      (chainValueState_block s pc valid0 valid8) (digit_block copied copiedPC validDigit),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [digit_pc,copiedPC]; rfl
  · rw [reg.1,chainValueState_chain,chainEq,addr,chainValueState_digit,digitEq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have := digit.isLt
    omega
  · rw [reg.2.1,chainValueState_chain,chainEq]
  · exact reg.2.2.1
  · rw [keep _ (by decide) (by decide)]; exact levelEq
  · rw [keep _ (by decide) (by decide)]; exact leafEq
  · rw [keep _ (by decide) (by decide)]; exact chainEq
  · intro i
    rw [keep _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact indexEq i
  · intro i
    fin_cases i
    · change ready.getMem 0x80020 = _
      rw [digit_mem,chainValueState_mem,if_neg (by decide),if_pos rfl]
      exact value0
    · change ready.getMem 0x80028 = _
      rw [digit_mem,chainValueState_mem,if_pos rfl]
      exact value8
  · exact sticky1.1.trans sticky0.1
  · exact sticky1.2.1.trans sticky0.2.1
  · exact sticky1.2.2.trans sticky0.2.2
  · exact reg.2.2.2.1.trans (chainValueState_stack s).1
  · exact reg.2.2.2.2.trans (chainValueState_stack s).2
  · intro a low high
    exact keep a low high

end SigGolfCandidate.Hypertree.Verifying.Hoist
