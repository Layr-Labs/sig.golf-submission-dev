import SigGolfCandidate.Hypertree.VerifyHoistWitness
namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing
set_option linter.unusedSimpArgs false
private def liftStart (s : MachineState) : MachineState := s.setPC 0x1490
private theorem prefix_eq (s : MachineState)
    (pc : s.pc = 0x1498) (base : s.getReg .x28 = 0x80000)
    (counter : s.getReg .x6 = s.getMem 0x80430) :
    execInstrBr (execInstrBr (liftStart s) (.LUI .x28 0x80))
      (.LD .x6 .x28 0x430) = s := by
  cases s with
  | mk regs mem code p commits pubs priv buf =>
    dsimp [liftStart, execInstrBr, MachineState.getReg, MachineState.getMem,
      MachineState.setReg, MachineState.setPC] at *
    have addr : (524288#64 : Word) + signExtend12 (1072#12) = 525360#64 := by decide
    rw [addr, ←counter, ←base, ←pc]
    congr 1
    funext r
    by_cases h6 : r = .x6
    · subst r; simp
    by_cases h28 : r = .x28
    · subst r; simp
    simp [h6, h28]

private def resumeValueState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x7 .x28 0x448)
  let s := execInstrBr s (.SLLI .x10 .x6 4)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.SD .x28 .x10 0x20)
  execInstrBr s (.SD .x28 .x11 0x28)

private theorem resumeValueState_eq (s : MachineState)
    (pc : s.pc = 0x1498) (base : s.getReg .x28 = 0x80000)
    (counter : s.getReg .x6 = s.getMem 0x80430) :
    resumeValueState s = chainValueState (liftStart s) := by
  simp only [resumeValueState, chainValueState, prefix_eq s pc base counter]


private theorem resumeValueState_block (s : MachineState)
    (pc : s.pc = 0x1498) (base : s.getReg .x28 = 0x80000)
    (counter : s.getReg .x6 = s.getMem 0x80430)
    (valid0 : accessValid (chainSource s) 8 = true)
    (valid8 : accessValid (chainSource s + 8) 8 = true) :
    OrdinarySteps verify s 7 (resumeValueState s) := by
  let s1 := execInstrBr s (.LD .x7 .x28 0x448)
  let s2 := execInstrBr s1 (.SLLI .x10 .x6 4)
  let s3 := execInstrBr s2 (.ADD .x7 .x7 .x10)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.SD .x28 .x10 0x20)
  let s7 := execInstrBr s6 (.SD .x28 .x11 0x28)
  apply OrdinarySteps.step s s1 _ (.base (.LD .x7 .x28 0x448)) 6
  · simp only [fetch, pc]; decide
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12,
      base, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s1 s2 _ (.base (.SLLI .x10 .x6 4)) 5
  · have hp : s1.pc = 0x149c := by simp [s1, execInstrBr, pc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x7 .x7 .x10)) 4
  · have hp : s2.pc = 0x14a0 := by simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 3
  · have hp : s3.pc = 0x14a4 := by simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      base, counter, chainSource] using valid0
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 2
  · have hp : s4.pc = 0x14a8 := by simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simpa [s1, s2, s3, s4, s5, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      base, counter, chainSource] using valid8
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x10 0x20)) 1
  · have hp : s5.pc = 0x14ac := by simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, base, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x11 0x28)) 0
  · have hp : s6.pc = 0x14b0 := by simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
    simp only [fetch, hp]; decide
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid,
      execInstrBr, signExtend12, base, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _


/-- Reuse the endpoint block's live base and next-chain counter to enter at PC 0x1498. -/
theorem witness_prepare_after_endpoint (s : MachineState) (level tree : Nat) (side : Bool)
    (chain : Reference.Chain) (digit : Fin 8) (value : Reference.Digest)
    (pc : s.pc = 0x1498)
    (baseReg : s.getReg .x28 = 0x80000)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
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
  have counterReg : s.getReg .x6 = s.getMem 0x80430 := chainReg.trans chainEq.symm
  let copied := resumeValueState s
  have copiedEq : copied = chainValueState (liftStart s) :=
    resumeValueState_eq s pc baseReg counterReg
  have copiedPC : copied.pc = 0x14b4 := by
    rw [copiedEq, chainValueState_pc]
    rfl
  have copiedBase : copied.getReg .x28 = 0x80000 := by
    rw [copiedEq, chainValueState_base]
  have copiedChain : copied.getReg .x6 = BitVec.ofNat 64 chain.val := by
    rw [copiedEq, chainValueState_chain]
    exact chainEq
  have copiedMem (a : Word) : copied.getMem a =
      if a = 0x80028 then s.getMem (chainSource s + 8) else
      if a = 0x80020 then s.getMem (chainSource s) else s.getMem a := by
    rw [copiedEq, chainValueState_mem]
    rfl
  have addr : (0x80600 : Word) + BitVec.ofNat 64 chain.val =
      BitVec.ofNat 64 (0x80600 + chain.val) := (BitVec.ofNat_add _ _).symm
  have validDigit : accessValid (0x80600 + copied.getReg .x6) 1 = true := by
    rw [copiedChain, addr]
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, MEMORY_BYTES,
      Nat.mod_one, decide_true, Bool.and_true, decide_eq_true_eq]
    have := chain.isLt
    omega
  have copiedDigit : copied.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) =
      s.getByte (BitVec.ofNat 64 (0x80600 + chain.val)) := by
    rw [copiedEq, chainValueState_digit]
    rfl
  have keep (a : Word) (low : a ≠ 0x80020) (high : a ≠ 0x80028) :
      (digitState copied).getMem a = s.getMem a := by
    rw [digit_mem, copiedMem, if_neg high, if_neg low]
  let ready := digitState copied
  have reg := digit_regs copied copiedBase
  have sticky0 : copied.getReg .x5 = s.getReg .x5 ∧
      copied.getReg .x12 = s.getReg .x12 ∧ copied.getReg .x31 = s.getReg .x31 := by
    rw [copiedEq]
    exact chainValueState_sticky (liftStart s)
  have sticky1 := digit_sticky copied
  have stack0 : copied.getReg .x1 = s.getReg .x1 ∧
      copied.getReg .x2 = s.getReg .x2 := by
    rw [copiedEq]
    exact chainValueState_stack (liftStart s)
  refine ⟨ready, ordinary_trans verify s copied ready 7 5
      (resumeValueState_block s pc baseReg counterReg valid0 valid8)
      (digit_block copied copiedPC copiedBase validDigit),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact digit_pc copied copiedPC
  · rw [reg.1, copiedChain, addr, copiedDigit, digitEq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := digit.isLt
    omega
  · rw [reg.2.1, copiedChain]
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
      rw [digit_mem, copiedMem, if_neg (by decide), if_pos rfl]
      exact value0
    · change ready.getMem 0x80028 = _
      rw [digit_mem, copiedMem, if_pos rfl]
      exact value8
  · exact sticky1.1.trans sticky0.1
  · exact sticky1.2.1.trans sticky0.2.1
  · exact sticky1.2.2.trans sticky0.2.2
  · exact reg.2.2.2.1.trans stack0.1
  · exact reg.2.2.2.2.trans stack0.2
  · intro a low high
    exact keep a low high

/-- info: 'SigGolfCandidate.Hypertree.Verifying.Hoist.witness_prepare_after_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.Hypertree.Verifying.Hoist.witness_prepare_after_endpoint

end SigGolfCandidate.Hypertree.Verifying.Hoist
