import SigGolfCandidate.Hypertree.VerifyHoistLoop

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def chainSource (s : MachineState) : Word := s.getMem 0x80448 + (s.getMem 0x80430 <<< 4)

def chainValueState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.LD .x6 .x28 0x430)
  let s := execInstrBr s (.LD .x7 .x28 0x448)
  let s := execInstrBr s (.SLLI .x18 .x6 4)
  let s := execInstrBr s (.ADD .x7 .x7 .x18)
  let s := execInstrBr s (.LD .x18 .x7 0)
  let s := execInstrBr s (.LD .x19 .x7 8)
  let s := execInstrBr s (.SD .x28 .x18 0x20)
  execInstrBr s (.SD .x28 .x19 0x28)

theorem chainValueState_block (s : MachineState) (pc : s.pc = 0x1490)
    (valid0 : accessValid (chainSource s) 8 = true) (valid8 : accessValid (chainSource s + 8) 8 = true) :
    OrdinarySteps verify s 9 (chainValueState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.LD .x6 .x28 0x430)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0x448)
  let s4 := execInstrBr s3 (.SLLI .x18 .x6 4)
  let s5 := execInstrBr s4 (.ADD .x7 .x7 .x18)
  let s6 := execInstrBr s5 (.LD .x18 .x7 0)
  let s7 := execInstrBr s6 (.LD .x19 .x7 8)
  let s8 := execInstrBr s7 (.SD .x28 .x18 0x20)
  let s9 := execInstrBr s8 (.SD .x28 .x19 0x28)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s.pc = 0x1490 := by simp [execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x6 .x28 0x430)) 7
  · have hp : s1.pc = 0x1494 := by simp [s1, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0x448)) 6
  · have hp : s2.pc = 0x1498 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x18 .x6 4)) 5
  · have hp : s3.pc = 0x149c := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADD .x7 .x7 .x18)) 4
  · have hp : s4.pc = 0x14a0 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x18 .x7 0)) 3
  · have hp : s5.pc = 0x14a4 := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, chainSource] using valid0
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x19 .x7 8)) 2
  · have hp : s6.pc = 0x14a8 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, chainSource] using valid8
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x18 0x20)) 1
  · have hp : s7.pc = 0x14ac := by simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x19 0x28)) 0
  · have hp : s8.pc = 0x14b0 := by simp [s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem chainValueState_mem (s : MachineState) (a : Word) :
    (chainValueState s).getMem a = if a = 0x80028 then s.getMem (chainSource s + 8) else
      if a = 0x80020 then s.getMem (chainSource s) else s.getMem a := by
  simp [chainValueState, chainSource, execInstrBr, signExtend12, Expansion.mem_setMem,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_chain (s : MachineState) :
    (chainValueState s).getReg .x6 = s.getMem 0x80430 := by
  simp [chainValueState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem chainValueState_pc (s : MachineState) : (chainValueState s).pc = s.pc + 36 := by
  simp [chainValueState, execInstrBr, BitVec.add_assoc]

theorem chainValueState_base (s : MachineState) :
    (chainValueState s).getReg .x28 = 0x80000 := by
  simp [chainValueState, execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem chainValueState_stack (s : MachineState) :
    (chainValueState s).getReg .x1 = s.getReg .x1 ∧ (chainValueState s).getReg .x2 = s.getReg .x2 := by
  simp [chainValueState, execInstrBr, MachineState.getReg_setReg_ne]

def digitState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADD .x7 .x28 .x6)
  let s := execInstrBr s (.LBU .x30 .x7 0x600)
  execInstrBr s (.JAL .x0 1104)

theorem digit_address (x : Word) :
    (0x80000 : Word) + x + signExtend12 (0x600 : BitVec 12) = 0x80600 + x := by
  have h : signExtend12 (0x600 : BitVec 12) = (0x600 : Word) := by decide
  rw [h]
  bv_omega

theorem digit_block (s : MachineState) (pc : s.pc = 0x14b4)
    (base : s.getReg .x28 = 0x80000)
    (valid : accessValid (0x80600 + s.getReg .x6) 1 = true) :
    OrdinarySteps verify s 3 (digitState s) := by
  let s1 := execInstrBr s (.ADD .x7 .x28 .x6)
  let s2 := execInstrBr s1 (.LBU .x30 .x7 0x600)
  let s3 := execInstrBr s2 (.JAL .x0 1104)
  apply OrdinarySteps.step s s1 _ (.base (.ADD .x7 .x28 .x6)) 2
  · have hp : s.pc = 0x14b4 := pc
    simp only [fetch,hp]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LBU .x30 .x7 0x600)) 1
  · have hp : s1.pc = 0x14b8 := by simp [s1,execInstrBr,pc]
    simp only [fetch,hp]; decide
  · have v : accessValid (0x80000 + s.getReg .x6 + signExtend12 (0x600 : BitVec 12)) 1 = true := by
      rw [digit_address]; exact valid
    simpa [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,base] using v
  apply OrdinarySteps.step s2 s3 _ (.base (.JAL .x0 1104)) 0
  · have hp : s2.pc = 0x14bc := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simp only [fetch,hp]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem digit_mem (s : MachineState) (a : Word) :
    (digitState s).getMem a = s.getMem a := by
  simp [digitState,execInstrBr]

theorem digit_pc (s : MachineState) (pc : s.pc = 0x14b4) :
    (digitState s).pc = 0x190c := by
  norm_num [digitState,execInstrBr,pc,signExtend21]
  decide

theorem digit_regs (s : MachineState) (base : s.getReg .x28 = 0x80000) :
    (digitState s).getReg .x30 = (s.getByte (0x80600 + s.getReg .x6)).zeroExtend 64 ∧
    (digitState s).getReg .x6 = s.getReg .x6 ∧
    (digitState s).getReg .x28 = 0x80000 ∧
    (digitState s).getReg .x1 = s.getReg .x1 ∧
    (digitState s).getReg .x2 = s.getReg .x2 := by
  have addr : s.getByte (0x80000 + s.getReg .x6 + signExtend12 (0x600 : BitVec 12)) =
      s.getByte (0x80600 + s.getReg .x6) := by rw [digit_address]
  simp [digitState,execInstrBr,base,addr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact congrArg (BitVec.setWidth 64) addr

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
    (chainValueState s).getReg .x31 = s.getReg .x31 ∧
    (chainValueState s).getReg .x10 = s.getReg .x10 ∧
    (chainValueState s).getReg .x11 = s.getReg .x11 := by
  simp [chainValueState,execInstrBr,MachineState.getReg_setReg_ne]

theorem digit_sticky (s : MachineState) :
    (digitState s).getReg .x5 = s.getReg .x5 ∧
    (digitState s).getReg .x12 = s.getReg .x12 ∧
    (digitState s).getReg .x31 = s.getReg .x31 ∧
    (digitState s).getReg .x10 = s.getReg .x10 ∧
    (digitState s).getReg .x11 = s.getReg .x11 := by
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
    ∃ ready, OrdinarySteps verify s 12 ready ∧ ready.pc = 0x190c ∧
      ready.getReg .x30 = BitVec.ofNat 64 digit.val ∧
      ready.getReg .x6 = BitVec.ofNat 64 chain.val ∧
      ready.getReg .x28 = 0x80000 ∧
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
      ready.getReg .x10 = s.getReg .x10 ∧
      ready.getReg .x11 = s.getReg .x11 ∧
      ready.getReg .x1 = s.getReg .x1 ∧
      ready.getReg .x2 = s.getReg .x2 ∧
      (∀ a, a ≠ 0x80020 → a ≠ 0x80028 → ready.getMem a = s.getMem a) := by
  let copied := chainValueState s
  have copiedPC : copied.pc = 0x14b4 := by rw [chainValueState_pc,pc]; rfl
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
  have reg := digit_regs copied (chainValueState_base s)
  have sticky0 := chainValueState_sticky s
  have sticky1 := digit_sticky copied
  refine ⟨ready,ordinary_trans verify s copied ready 9 3
      (chainValueState_block s pc valid0 valid8)
      (digit_block copied copiedPC (chainValueState_base s) validDigit),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact digit_pc copied copiedPC
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
  · exact sticky1.2.2.1.trans sticky0.2.2.1
  · exact sticky1.2.2.2.1.trans sticky0.2.2.2.1
  · exact sticky1.2.2.2.2.trans sticky0.2.2.2.2
  · exact reg.2.2.2.1.trans (chainValueState_stack s).1
  · exact reg.2.2.2.2.trans (chainValueState_stack s).2
  · intro a low high
    exact keep a low high

end SigGolfCandidate.Hypertree.Verifying.Hoist
