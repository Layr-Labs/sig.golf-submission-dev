import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureCompose67
import SigGolfCandidate.Hypertree.KeygenTrace
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstAnswer67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67

/-! One H2 compression in the upper WOTS signer, including the byte header update
and the increment that precedes the next selected-value capture. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Tick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def staged (s : MachineState) : MachineState :=
  execInstrBr s (.SB .x10 .x21 4)

def answered (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (staged s) (hash (hashInput (staged s)))

def advanced (hash : Hash) (s : MachineState) : MachineState :=
  execInstrBr (answered hash s) (.ADDI .x21 .x21 1)

private theorem tick_code :
    Keygen.instructionAt image 0x1a38 = some (.base (.SB .x10 .x21 4)) ∧
    Keygen.instructionAt image 0x1a3c = some (.base .ECALL) ∧
    Keygen.instructionAt image 0x1a40 = some (.base (.ADDI .x21 .x21 1)) := by
  decide

theorem stage_steps (s : MachineState) (pc : s.pc = 0x1a38)
    (source : s.getReg .x10 = 0x80000) :
    OrdinarySteps image s 1 (staged s) := by
  apply OrdinarySteps.step s (staged s) _ (.base (.SB .x10 .x21 4)) 0
  · simpa only [Keygen.fetch_at, pc] using tick_code.1
  · change (if accessValid (s.getReg .x10 + signExtend12 (4 : BitVec 12)) 1
      then some (staged s) else none) = some (staged s)
    simp [source, signExtend12, accessValid, rangeValid, MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem staged_pc (s : MachineState) (pc : s.pc = 0x1a38) :
    (staged s).pc = 0x1a3c := by
  simp [staged, execInstrBr, pc]

theorem staged_regs (s : MachineState) :
    (staged s).getReg .x5 = s.getReg .x5 ∧
    (staged s).getReg .x10 = s.getReg .x10 ∧
    (staged s).getReg .x11 = s.getReg .x11 ∧
    (staged s).getReg .x12 = s.getReg .x12 ∧
    (staged s).getReg .x19 = s.getReg .x19 ∧
    (staged s).getReg .x20 = s.getReg .x20 ∧
    (staged s).getReg .x21 = s.getReg .x21 := by
  simp [staged, execInstrBr]

theorem stage_mem (s : MachineState)
    (source : s.getReg .x10 = 0x80000) (a : Word) :
    (staged s).getMem a =
      if a = 0x80000 then
        replaceByte (s.getMem 0x80000) 4 ((s.getReg .x21).truncate 8)
      else s.getMem a := by
  simp [staged, execInstrBr, MachineState.setByte, source,
    alignToDword, byteOffset, signExtend12]

theorem replaceByte_override4 (w : Word) (old current : BitVec 8) :
    replaceByte (replaceByte w 4 old) 4 current = replaceByte w 4 current := by
  ext i hi
  interval_cases i <;> simp [replaceByte, BitVec.getElem_or, BitVec.getElem_and]

theorem stage_header (s : MachineState) (base chain old step : Nat)
    (source : s.getReg .x10 = 0x80000)
    (stepReg : s.getReg .x21 = BitVec.ofNat 64 step)
    (header : s.getMem 0x80000 = KeygenDomain.header 2 base 0 chain old)
    (baseBound : base < 256) (chainBound : chain < 256)
    (oldBound : old < 256) (stepBound : step < 256) :
    (staged s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain step := by
  rw [stage_mem s source 0x80000,if_pos rfl,header,stepReg]
  have low : (BitVec.ofNat 64 step).truncate 8 = BitVec.ofNat 8 step := by
    simp
  rw [low]
  exact GroupedBalancedByteFastSuffixData67.header_step_replace
    base chain old step baseBound chainBound oldBound stepBound

theorem staged_query (s : MachineState) (base leaf chain step : Nat)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (value : Reference.Digest)
    (words : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    hashInput (staged s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 base 0 chain step) leaf value) := by
  obtain ⟨_, src, len, _, _, _, _⟩ := staged_regs s
  apply KeygenDomain.query_eq (staged s)
    (KeygenDomain.header 2 base 0 chain step) leaf value
      (src.trans source) (len.trans bits)
  apply KeygenDomain.words_of_layout (staged s)
    (KeygenDomain.header 2 base 0 chain step) leaf value
  · rw [stage_mem s source, if_pos rfl, header]
  · intro i
    rw [stage_mem s source, if_neg (by fin_cases i <;> decide)]
    exact tree i
  · intro i
    rw [stage_mem s source, if_neg (by fin_cases i <;> decide)]
    exact words i

theorem answered_words (hash : Hash) (s : MachineState)
    (base leaf step : Nat) (chain : GroupedBalancedUpperTree67.ChainMixed)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (value : Reference.Digest)
    (words : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (answered hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base leaf
          chain step value).extractLsb' (64*i.val) 64 := by
  have query := staged_query s base leaf chain.val step source bits
    header tree value words
  have dst := (staged_regs s).2.2.2.1.trans destination
  intro i
  rw [answered,
    GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_word (staged s)
      (hash (hashInput (staged s))) dst
      ⟨i.val, by have := i.isLt; omega⟩]
  rw [query]
  let answer := Reference.query hash 2 base leaf 0 chain.val step
    (bytes value)
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem tick_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a38)
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    Trace hash image s 3 10 1 1 (advanced hash s) := by
  have first := stage_steps s pc source
  have stagedPc := staged_pc s pc
  obtain ⟨service', source', bits', dest', _, _, _⟩ := staged_regs s
  have code : fetch image (staged s) = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at, stagedPc] using tick_code.2.1
  have valid : hashArgumentsValid (staged s) = true := by
    rw [hashArgumentsValid, source', source, bits', bits, dest', destination]
    simp [
      accessValid, rangeValid, MEMORY_BYTES]
  have len : (hashInput (staged s)).1 = 384 := by
    simp [hashInput, bits', bits]
  have htrace : Trace hash image (staged s) 1 8 1 1 (answered hash s) := by
    simpa [answered, len, compressions] using
      Trace.hash (staged s) _ 0 0 0 0 code
        (service'.trans service) valid (Trace.refl _)
  have answerPc : (answered hash s).pc = 0x1a40 := by
    simp [answered, writeHash, stagedPc]
  have finalOrd : OrdinarySteps image (answered hash s) 1 (advanced hash s) := by
    apply OrdinarySteps.step (answered hash s) (advanced hash s) _
      (.base (.ADDI .x21 .x21 1)) 0
    · simpa only [Keygen.fetch_at, answerPc] using tick_code.2.2
    · rfl
    exact OrdinarySteps.refl _
  have whole := (OrdinarySteps.trace (hash := hash) first).trans
    (htrace.trans (OrdinarySteps.trace (hash := hash) finalOrd))
  simpa only [Nat.reduceAdd] using whole

theorem advanced_pc (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a38) :
    (advanced hash s).pc = 0x1a44 := by
  simp [advanced, answered, staged, writeHash, execInstrBr, pc]

theorem advanced_regs (hash : Hash) (s : MachineState) :
    (advanced hash s).getReg .x21 = s.getReg .x21 + 1 ∧
    (advanced hash s).getReg .x20 = s.getReg .x20 ∧
    (advanced hash s).getReg .x19 = s.getReg .x19 ∧
    (advanced hash s).getReg .x5 = s.getReg .x5 ∧
    (advanced hash s).getReg .x10 = s.getReg .x10 ∧
    (advanced hash s).getReg .x11 = s.getReg .x11 ∧
    (advanced hash s).getReg .x12 = s.getReg .x12 := by
  simp [advanced, answered, staged, writeHash, execInstrBr,
    signExtend12,
    MachineState.setByte, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem advanced_stack (hash : Hash) (s : MachineState) :
    (advanced hash s).getReg .x2 = s.getReg .x2 := by
  simp [advanced, answered, staged, writeHash, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem advanced_words (hash : Hash) (s : MachineState)
    (destination : s.getReg .x12 = 0x80020) :
    ∀ i : Fin 2,
      (advanced hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (hash (hashInput (staged s))).extractLsb' (64*i.val) 64 := by
  intro i
  have dst := (staged_regs s).2.2.2.1.trans destination
  simpa only [advanced,answered,execInstrBr,
    MachineState.getMem_setPC,MachineState.getMem_setReg] using
    GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_word
      (staged s) (hash (hashInput (staged s))) dst
      ⟨i.val,by have := i.isLt; omega⟩

theorem advanced_frame (hash : Hash) (s : MachineState)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (a : Word) (h0 : a ≠ 0x80000)
    (hout : ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) :
    (advanced hash s).getMem a = s.getMem a := by
  have dst := (staged_regs s).2.2.2.1.trans destination
  simp only [advanced,answered,execInstrBr,
    MachineState.getMem_setPC,MachineState.getMem_setReg]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (staged s) (hash (hashInput (staged s))) dst a hout]
  rw [stage_mem s source a,if_neg h0]

theorem advanced_header (hash : Hash) (s : MachineState)
    (base chain old step : Nat)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (stepReg : s.getReg .x21 = BitVec.ofNat 64 step)
    (header : s.getMem 0x80000 = KeygenDomain.header 2 base 0 chain old)
    (baseBound : base < 256) (chainBound : chain < 256)
    (oldBound : old < 256) (stepBound : step < 256) :
    (advanced hash s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain step := by
  have dst := (staged_regs s).2.2.2.1.trans destination
  simp only [advanced,answered,execInstrBr,
    MachineState.getMem_setPC,MachineState.getMem_setReg]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (staged s) (hash (hashInput (staged s))) dst 0x80000
    (by intro i; fin_cases i <;> decide)]
  exact stage_header s base chain old step source stepReg header
    baseBound chainBound oldBound stepBound

theorem advanced_chain_words (hash : Hash) (s : MachineState)
    (base leaf step : Nat) (chain : GroupedBalancedUpperTree67.ChainMixed)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (value : Reference.Digest)
    (words : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (advanced hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base leaf
          chain step value).extractLsb' (64*i.val) 64 := by
  intro i
  simpa only [advanced,execInstrBr,MachineState.getMem_setPC,
    MachineState.getMem_setReg] using
    answered_words hash s base leaf step chain source bits destination
      header tree value words i

#print axioms tick_trace
#print axioms answered_words
#print axioms advanced_frame
#print axioms advanced_header
#print axioms advanced_chain_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Tick67
