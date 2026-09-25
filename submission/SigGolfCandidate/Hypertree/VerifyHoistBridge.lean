import SigGolfCandidate.Hypertree.VerifyHoistPrepare
import SigGolfCandidate.Hypertree.VerifyHoistWord
import SigGolfCandidate.Hypertree.VerifyHoistLoop

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Signing Keygen
set_option maxRecDepth 4096

theorem entry_pc (s : MachineState) (pc : s.pc = 0x190c) :
    (entryState s).pc = if s.getReg .x6 = 0 then 0x1924 else 0x1910 := by
  simp [entryState, execInstrBr, pc, signExtend21, signExtend13,
    MachineState.getReg_setReg_ne]

theorem entry_mem (s : MachineState) (a : Word) :
    (entryState s).getMem a = s.getMem a := by
  simp [entryState, execInstrBr]

theorem entry_regs (s : MachineState) :
    (entryState s).getReg .x6 = s.getReg .x6 ∧
    (entryState s).getReg .x10 = s.getReg .x10 ∧
    (entryState s).getReg .x28 = s.getReg .x28 ∧
    (entryState s).getReg .x30 = s.getReg .x30 ∧
    (entryState s).getReg .x1 = s.getReg .x1 ∧
    (entryState s).getReg .x2 = s.getReg .x2 := by
  simp [entryState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_sticky (s : MachineState) :
    (entryState s).getReg .x5 = s.getReg .x5 ∧
    (entryState s).getReg .x12 = s.getReg .x12 ∧
    (entryState s).getReg .x31 = s.getReg .x31 := by
  simp [entryState,execInstrBr,MachineState.getReg_setReg_ne]

theorem full_mem (s : MachineState) (stepPtr : s.getReg .x28 = 0x80438) (a : Word) :
    (fullState s).getMem a =
      if a = 0x80438 then s.getReg .x30 else s.getMem a := by
  simp [fullState, execInstrBr, stepPtr, signExtend12, Expansion.mem_setMem]

theorem full_regs (s : MachineState) :
    (fullState s).getReg .x5 = s.getReg .x5 ∧
    (fullState s).getReg .x10 = s.getReg .x10 ∧
    (fullState s).getReg .x11 = s.getReg .x11 ∧
    (fullState s).getReg .x12 = s.getReg .x12 ∧
    (fullState s).getReg .x28 = s.getReg .x28 ∧
    (fullState s).getReg .x30 = s.getReg .x30 ∧
    (fullState s).getReg .x31 = 7 ∧
    (fullState s).getReg .x1 = s.getReg .x1 ∧
    (fullState s).getReg .x2 = s.getReg .x2 := by
  simp [fullState, execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem header_jump_pc (s : MachineState) (pc : s.pc = 0x15ec) :
    (execInstrBr s (.JAL .x0 836)).pc = 0x1930 := by
  norm_num [execInstrBr, pc, signExtend21]
  decide

theorem header_jump_mem (s : MachineState) (a : Word) :
    (execInstrBr s (.JAL .x0 836)).getMem a = s.getMem a := by
  simp [execInstrBr]

theorem header_jump_regs (s : MachineState) :
    (execInstrBr s (.JAL .x0 836)).getReg .x1 = s.getReg .x1 ∧
    (execInstrBr s (.JAL .x0 836)).getReg .x2 = s.getReg .x2 := by
  simp [execInstrBr, MachineState.getReg_setReg_ne]

theorem header_jump_regs_all (s : MachineState) (r : Reg) :
    (execInstrBr s (.JAL .x0 836)).getReg r = s.getReg r := by
  by_cases h : r = .x0
  · subst r
    simp only [execInstrBr,MachineState.getReg_setPC,
      MachineState.setReg,MachineState.getReg]
  · simp only [execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne s .x0 r (s.pc+4) (Ne.symm h)

theorem header_jump_loop_data (s : MachineState) (level tree step : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (data : LoopData s level tree side chain step value) :
    LoopData (execInstrBr s (.JAL .x0 836)) level tree side chain step value :=
  data.of_mem_regs (header_jump_mem s) (header_jump_regs_all s)

/-- Building the full header on chain zero establishes the persistent word invariant. -/
theorem full_header_word_carry (s : MachineState) (level tree leaf chain step : Nat)
    (value : Reference.Digest)
    (chainBound : chain < 46) (stepBound : step < 8)
    (stepPtr : s.getReg .x28 = 0x80438)
    (stepReg : s.getReg .x30 = BitVec.ofNat 64 step)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 leaf)
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64) :
    HeaderWordCarry (VerifyChainHeaderDirect.state (fullState s)) level tree leaf := by
  let prepared := fullState s
  have keep (a : Word) (ne : a ≠ 0x80438) : prepared.getMem a = s.getMem a := by
    rw [full_mem s stepPtr, if_neg ne]
  have preparedLevel : prepared.getMem 0x80400 = BitVec.ofNat 64 level :=
    (keep _ (by decide)).trans levelEq
  have preparedLeaf : prepared.getMem 0x80428 = BitVec.ofNat 64 leaf :=
    (keep _ (by decide)).trans leafEq
  have preparedChain : prepared.getMem 0x80430 = BitVec.ofNat 64 chain :=
    (keep _ (by decide)).trans chainEq
  have preparedStep : prepared.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [full_mem s stepPtr, if_pos rfl, stepReg]
  have preparedIndex : ∀ i : Fin 3, prepared.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    exact (keep _ (by fin_cases i <;> decide)).trans (indexEq i)
  have preparedValue : ∀ i : Fin 2, prepared.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by
    intro i
    exact (keep _ (by fin_cases i <;> decide)).trans (valueEq i)
  have words := VerifyChainHeaderDirect.words prepared level tree leaf chain step value
    preparedLevel preparedLeaf preparedChain preparedStep preparedIndex preparedValue
  obtain ⟨service, _, _, destination⟩ := VerifyChainHeaderDirect.regs prepared
  have seven : (VerifyChainHeaderDirect.state prepared).getReg .x31 = 7 := by
    have reg : (VerifyChainHeaderDirect.state prepared).getReg .x31 = prepared.getReg .x31 := by
      simp [VerifyChainHeaderDirect.state, execInstrBr, MachineState.getReg_setReg_ne]
    exact reg.trans (full_regs s).2.2.2.2.2.2.1
  refine ⟨chain, step, chainBound, stepBound, ?_, ?_, service, destination, seven⟩
  · simpa [KeygenDomain.inputWord, wordAddress] using words (0 : Fin 6)
  · intro i
    have w := words ⟨i.val+1, by have := i.isLt; omega⟩
    fin_cases i <;> simpa [KeygenDomain.inputWord, wordAddress] using w

/-- info: 'SigGolfCandidate.Hypertree.Verifying.Hoist.full_header_word_carry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms full_header_word_carry

/-- The short header update prepares the exact next HASH query. -/
theorem partial_loop_data (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (step : Nat)
    (value : Reference.Digest)
    (carry : HeaderWordCarry s level tree (Reference.sideNumber side))
    (levelBound : level < 256) (stepBound : step < 8)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (stepReg : s.getReg .x30 = BitVec.ofNat 64 step)
    (valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64) :
    LoopData (partialState s) level tree side chain step value := by
  rcases carry with ⟨oldChain,oldStep,oldChainBound,oldStepBound,
    header,index,service,destination,seven⟩
  have leafBound : Reference.sideNumber side < 256 := by cases side <;> decide
  have truncateChain : ((BitVec.ofNat 64 chain.val).truncate 8) =
      BitVec.ofNat 8 chain.val := by
    rw [BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
  have truncateStep : ((BitVec.ofNat 64 step).truncate 8) =
      BitVec.ofNat 8 step := by
    rw [BitVec.truncate_eq_setWidth,
      BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)]
  obtain ⟨r5,r10,r11,r12,r30,r31⟩ := partial_regs s
  constructor
  · rw [partial_mem,if_pos rfl,header,chainReg,stepReg,
      truncateChain,truncateStep]
    exact header_chain_step_replace level (Reference.sideNumber side)
      oldChain oldStep chain.val step levelBound leafBound
      (by omega) (by omega) (by have := chain.isLt; omega) (by omega)
  · intro i
    rw [partial_mem,if_neg (by fin_cases i <;> decide)]
    exact index i
  · intro i
    rw [partial_mem,if_neg (by fin_cases i <;> decide)]
    exact valueEq i
  · exact r10
  · exact r11
  · exact r12.trans destination
  · exact r5.trans service
  · exact r30.trans stepReg
  · exact r31.trans seven

/-- The chain-zero full header build prepares the exact first HASH query. -/
theorem full_loop_data (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (step : Nat)
    (value : Reference.Digest)
    (stepPtr : s.getReg .x28 = 0x80438)
    (stepReg : s.getReg .x30 = BitVec.ofNat 64 step)
    (stepBound : step < 8)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64) :
    LoopData (VerifyChainHeaderDirect.state (fullState s))
      level tree side chain step value := by
  let prepared := fullState s
  let final := VerifyChainHeaderDirect.state prepared
  have keep (a : Word) (ne : a ≠ 0x80438) :
      prepared.getMem a = s.getMem a := by
    rw [full_mem s stepPtr, if_neg ne]
  have preparedLevel := (keep 0x80400 (by decide)).trans levelEq
  have preparedLeaf := (keep 0x80428 (by decide)).trans leafEq
  have preparedChain := (keep 0x80430 (by decide)).trans chainEq
  have preparedStep : prepared.getMem 0x80438 = BitVec.ofNat 64 step := by
    rw [full_mem s stepPtr, if_pos rfl,stepReg]
  have preparedIndex : ∀ i : Fin 3, prepared.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    exact (keep _ (by fin_cases i <;> decide)).trans (indexEq i)
  have preparedValue : ∀ i : Fin 2, prepared.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64 := by
    intro i
    exact (keep _ (by fin_cases i <;> decide)).trans (valueEq i)
  have words := VerifyChainHeaderDirect.words prepared level tree
    (Reference.sideNumber side) chain.val step value
    preparedLevel preparedLeaf preparedChain preparedStep preparedIndex preparedValue
  obtain ⟨service,source,length,destination⟩ := VerifyChainHeaderDirect.regs prepared
  have carry := full_header_word_carry s level tree
    (Reference.sideNumber side) chain.val step value chain.isLt
    stepBound stepPtr stepReg levelEq leafEq chainEq indexEq valueEq
  rcases carry with ⟨_,_,_,_,_,canonicalIndex,_,_,seven⟩
  constructor
  · simpa [final,KeygenDomain.inputWord,wordAddress] using words (0 : Fin 6)
  · exact canonicalIndex
  · intro i
    rw [VerifyChainHeaderDirect.frame prepared _ (by
      fin_cases i <;> decide)]
    exact preparedValue i
  · exact source
  · exact length
  · exact destination
  · exact service
  · have same : final.getReg .x30 = prepared.getReg .x30 := by
      simp [final,VerifyChainHeaderDirect.state,execInstrBr,
        MachineState.getReg_setReg_ne]
    exact same.trans ((full_regs s).2.2.2.2.2.1.trans stepReg)
  · exact seven

def OutsideHeader (a : Word) : Prop :=
  a ≠ 0x80000 ∧ a ≠ 0x80008 ∧ a ≠ 0x80010 ∧
  a ≠ 0x80018 ∧ a ≠ 0x80438

/-- The two header paths meet at the same canonical HASH loop entry. -/
theorem prepare_header (s : MachineState) (level tree : Nat)
    (side : Bool) (chain : Reference.Chain) (digit : Fin 8)
    (value : Reference.Digest)
    (pc : s.pc = 0x190c)
    (chainReg : s.getReg .x6 = BitVec.ofNat 64 chain.val)
    (digitReg : s.getReg .x30 = BitVec.ofNat 64 digit.val)
    (stepPtr : s.getReg .x28 = 0x80438)
    (levelEq : s.getMem 0x80400 = BitVec.ofNat 64 level)
    (leafEq : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (chainEq : s.getMem 0x80430 = BitVec.ofNat 64 chain.val)
    (indexEq : ∀ i : Fin 3, s.getMem (wordAddress 0x80408 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueEq : ∀ i : Fin 2, s.getMem (wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64)
    (ready : HeaderReadyWord s level tree (Reference.sideNumber side) chain.val)
    (levelBound : level < 256) :
    ∃ prepared instructions,
      OrdinarySteps verify s instructions prepared ∧
      instructions = (if chain.val = 0 then 53 else 6) ∧
      prepared.pc = 0x1930 ∧
      LoopData prepared level tree side chain digit.val value ∧
      prepared.getReg .x1 = s.getReg .x1 ∧
      prepared.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideHeader a → prepared.getMem a = s.getMem a) := by
  let entered := entryState s
  have entryCode : EntryCode verify := by unfold EntryCode; decide
  have entryRun := entry_block verify entryCode s pc
  obtain ⟨e6,e10,e28,e30,e1,e2⟩ := entry_regs s
  have enteredChain : entered.getReg .x6 = BitVec.ofNat 64 chain.val := e6.trans chainReg
  have enteredStep : entered.getReg .x30 = BitVec.ofNat 64 digit.val := e30.trans digitReg
  have enteredPtr : entered.getReg .x28 = 0x80438 := e28.trans stepPtr
  have enteredLevel : entered.getMem 0x80400 = BitVec.ofNat 64 level :=
    (entry_mem s _).trans levelEq
  have enteredLeaf : entered.getMem 0x80428 =
      BitVec.ofNat 64 (Reference.sideNumber side) :=
    (entry_mem s _).trans leafEq
  have enteredChainMem : entered.getMem 0x80430 = BitVec.ofNat 64 chain.val :=
    (entry_mem s _).trans chainEq
  have enteredIndex : ∀ i : Fin 3,
      entered.getMem (wordAddress 0x80408 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    exact (entry_mem s _).trans (indexEq i)
  have enteredValue : ∀ i : Fin 2,
      entered.getMem (wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    exact (entry_mem s _).trans (valueEq i)
  by_cases zero : chain.val = 0
  · have atFull : entered.pc = 0x1924 := by
      rw [entry_pc s pc,chainReg,zero]
      rfl
    let full := fullState entered
    have fullCode : FullCode verify := by unfold FullCode; decide
    have fullRun := full_block verify fullCode entered atFull enteredPtr
    have fullPC := full_pc entered atFull
    let headed := VerifyChainHeaderDirect.state full
    have headerRun := VerifyChainHeaderDirect.block verify 0x152c
      VerifyChainHeaderDirect.verify_code full fullPC
    have headerPC : headed.pc = 0x15ec := by
      rw [VerifyChainHeaderDirect.pc,fullPC]
      decide
    let prepared := execInstrBr headed (.JAL .x0 836)
    have jumpCode : HeaderJumpCode verify := by unfold HeaderJumpCode; decide
    have jumpRun := header_jump verify jumpCode headed headerPC
    have headedData := full_loop_data entered level tree side chain digit.val
      value enteredPtr enteredStep digit.isLt enteredLevel enteredLeaf
      enteredChainMem enteredIndex enteredValue
    have preparedData := header_jump_loop_data headed level tree digit.val
      side chain value headedData
    refine ⟨prepared,53,?_,by simp [zero],
      header_jump_pc headed headerPC,preparedData,?_,?_,?_⟩
    · convert ordinary_trans verify s entered prepared 1 52 entryRun
        (ordinary_trans verify entered full prepared 3 49 fullRun
          (ordinary_trans verify full headed prepared 48 1 headerRun jumpRun)) using 1 <;> omega
    · exact (header_jump_regs headed).1.trans
        ((VerifyChainHeaderDirect.stack full).1.trans ((full_regs entered).2.2.2.2.2.2.2.1.trans e1))
    · exact (header_jump_regs headed).2.trans
        ((VerifyChainHeaderDirect.stack full).2.trans ((full_regs entered).2.2.2.2.2.2.2.2.trans e2))
    · intro a outside
      rw [header_jump_mem,VerifyChainHeaderDirect.frame full a (by
        intro i
        fin_cases i
        · simpa [wordAddress] using outside.1
        · simpa [wordAddress] using outside.2.1
        · simpa [wordAddress] using outside.2.2.1
        · simpa [wordAddress] using outside.2.2.2.1)]
      rw [full_mem entered enteredPtr a,if_neg outside.2.2.2.2]
      exact entry_mem s a
  · have atPartial : entered.pc = 0x1910 := by
      rw [entry_pc s pc,chainReg]
      have nonzeroReg : (BitVec.ofNat 64 chain.val) ≠ 0 := by
        intro h
        have natEq : chain.val = 0 := by
          have he := congrArg BitVec.toNat h
          change chain.val % 2^64 = 0 at he
          have := chain.isLt
          omega
        exact zero natEq
      simpa only [if_neg nonzeroReg]
    have oldCarry : HeaderWordCarry s level tree (Reference.sideNumber side) := by
      rcases ready with h | h
      · exact False.elim (zero h)
      · exact h
    have enteredCarry : HeaderWordCarry entered level tree (Reference.sideNumber side) := by
      rcases oldCarry with ⟨oldChain,oldStep,hc,hs,header,index,r5,r12,r31⟩
      obtain ⟨e5,e12,e31⟩ := entry_sticky s
      refine ⟨oldChain,oldStep,hc,hs,?_,?_,e5.trans r5,e12.trans r12,e31.trans r31⟩
      · exact (entry_mem s _).trans header
      · intro i; exact (entry_mem s _).trans (index i)
    let prepared := partialState entered
    have partialCode : PartialCode verify := by unfold PartialCode; decide
    have partialRun := partial_block verify partialCode entered atPartial
    have preparedData := partial_loop_data entered level tree side chain digit.val
      value enteredCarry levelBound digit.isLt enteredChain enteredStep enteredValue
    refine ⟨prepared,6,?_,by simp [zero],partial_pc entered atPartial,
      preparedData,?_,?_,?_⟩
    · convert ordinary_trans verify s entered prepared 1 5 entryRun partialRun using 1 <;> omega
    · have : prepared.getReg .x1 = entered.getReg .x1 := by
        simp [prepared,partialState,execInstrBr,MachineState.getReg_setReg_ne]
      exact this.trans e1
    · have : prepared.getReg .x2 = entered.getReg .x2 := by
        simp [prepared,partialState,execInstrBr,MachineState.getReg_setReg_ne]
      exact this.trans e2
    · intro a outside
      rw [partial_mem,if_neg outside.1]
      exact entry_mem s a

end SigGolfCandidate.Hypertree.Verifying.Hoist
