import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstAnswer67


/-! The WOTS loop increments its step and branches to the next H2 query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsLoopAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def advanceState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x21 .x21 1))
    (.BNE .x21 .x20 0x1ff4)

private theorem advance_code :
    Keygen.instructionAt image 0x12c8 = some (.base (.ADDI .x21 .x21 1)) ∧
    Keygen.instructionAt image 0x12cc = some (.base (.BNE .x21 .x20 0x1ff4)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x12c8) :
    OrdinarySteps image s 2 (advanceState s) := by
  let s1 := execInstrBr s (.ADDI .x21 .x21 1)
  obtain ⟨c0,c1⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x21 .x21 1)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 (advanceState s) _
    (.base (.BNE .x21 .x20 0x1ff4)) 0
  · have hp : s1.pc = 0x12cc := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem advance_fields (s : MachineState) (pc : s.pc = 0x12c8) :
    (advanceState s).pc =
      (if s.getReg .x21 + 1 ≠ s.getReg .x20 then 0x12c0 else 0x12d0) ∧
    (advanceState s).getReg .x21 = s.getReg .x21 + 1 ∧
    (advanceState s).getReg .x20 = s.getReg .x20 ∧
    (advanceState s).getReg .x19 = s.getReg .x19 ∧
    (∀ a : Word, (advanceState s).getMem a = s.getMem a) := by
  simp [advanceState,execInstrBr,pc,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_reg_stable (s : MachineState) (r : Reg)
    (different : r ≠ .x21) :
    (advanceState s).getReg r = s.getReg r := by
  cases r <;> simp_all [advanceState,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_mem (s : MachineState) (a : Word) :
    (advanceState s).getMem a = s.getMem a := by
  simp [advanceState,execInstrBr]

#print axioms advance_steps
#print axioms advance_fields

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsLoopAdvance67


/-! Reusable SB/HASH tick for a WOTS chain at PC 0x12c0. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def storeState (s : MachineState) : MachineState :=
  execInstrBr s (.SB .x10 .x21 4)

theorem store_code :
    Keygen.instructionAt image 0x12c0 = some (.base (.SB .x10 .x21 4)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem store_steps (s : MachineState)
    (pc : s.pc = 0x12c0) (source : s.getReg .x10 = 0x80000) :
    OrdinarySteps image s 1 (storeState s) := by
  apply OrdinarySteps.step s (storeState s) _
    (.base (.SB .x10 .x21 4)) 0
  · simpa only [Keygen.fetch_at,pc] using store_code
  · simp [storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      source,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem store_fields (s : MachineState) (pc : s.pc = 0x12c0) :
    (storeState s).pc = 0x12c4 ∧
    (∀ r : Reg, (storeState s).getReg r = s.getReg r) := by
  have getReg_setByte (t : MachineState) (a : Word) (b : Byte) (r : Reg) :
      (t.setByte a b).getReg r = t.getReg r := by
    simp [MachineState.setByte]
  constructor
  · simp [storeState,execInstrBr,pc]
  · intro r
    simp [storeState,execInstrBr,getReg_setByte]

theorem store_mem (s : MachineState) (source : s.getReg .x10 = 0x80000)
    (a : Word) :
    (storeState s).getMem a =
      if a = 0x80000 then
        replaceByte (s.getMem 0x80000) 4 ((s.getReg .x21).truncate 8)
      else s.getMem a := by
  simp [storeState,execInstrBr,MachineState.setByte,
    source,alignToDword,byteOffset,signExtend12]

theorem tick_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    Trace hash image s 2 9 1 1
      (writeHash (storeState s) (hash (hashInput (storeState s)))) := by
  obtain ⟨storedPC,regs⟩ := store_fields s pc
  have first : Trace hash image s 1 1 0 0 (storeState s) :=
    (store_steps s pc source).trace (hash := hash)
  have second := GroupedBalancedKeygenWotsFirstHash67.hash_trace
    hash (storeState s) storedPC
    ((regs .x5).trans service)
    ((regs .x10).trans source)
    ((regs .x11).trans bits)
    ((regs .x12).trans destination)
  simpa only [image,GroupedBalancedKeygenWotsFirstHash67.image,
    Nat.reduceAdd] using first.trans second

theorem tick_query (s : MachineState) (step : Nat)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 156 0 0 step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    hashInput (storeState s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 156 0 0 step) 0 seed) := by
  obtain ⟨_,regs⟩ := store_fields s pc
  have first : (storeState s).getMem 0x80000 =
      KeygenDomain.header 2 156 0 0 step := by
    rw [store_mem s source 0x80000,if_pos rfl,header]
  have index : ∀ i : Fin 3,
      (storeState s).getMem (Signing.wordAddress 0x80008 i.val) = 0 := by
    intro i
    rw [store_mem s source,if_neg]
    · exact tree i
    · fin_cases i <;> decide
  have data : ∀ i : Fin 2,
      (storeState s).getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
    intro i
    rw [store_mem s source,if_neg]
    · exact value i
    · fin_cases i <;> decide
  apply KeygenDomain.query_eq (storeState s)
    (KeygenDomain.header 2 156 0 0 step) 0 seed
  · exact (regs .x10).trans source
  · exact (regs .x11).trans bits
  · apply KeygenDomain.words_of_layout (storeState s)
      (KeygenDomain.header 2 156 0 0 step) 0 seed first
    · intro i
      simpa using index i
    · exact data

theorem tick_answer (hash : Hash) (s : MachineState) (step : Nat)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 156 0 0 step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (storeState s) (hash (hashInput (storeState s)))).getMem
        (Signing.wordAddress 0x80020 i.val) =
        (Reference.truncate
          (Reference.query hash 2 156 0 0 0 step (bytes seed))).extractLsb'
            (64*i.val) 64 := by
  have queryInput := tick_query s step pc source bits header tree seed value
  have query : hash (hashInput (storeState s)) =
      Reference.query hash 2 156 0 0 0 step (bytes seed) := by
    rw [queryInput]
    rfl
  have dst := (store_fields s pc).2 .x12 |>.trans destination
  intro i
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_word
    (storeState s) (hash (hashInput (storeState s))) dst
    ⟨i.val,by have := i.isLt; omega⟩,query]
  let answer := Reference.query hash 2 156 0 0 0 step (bytes seed)
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

#print axioms tick_trace
#print axioms tick_answer

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTick67
