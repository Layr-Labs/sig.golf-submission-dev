import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHashPrelude67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67. -/
section
/-! The first WOTS H2 call has a 48-byte input and writes to the seed buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHashPrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedKeygenImage67.image

def preludeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 32)
  let s := execInstrBr s (.ADDI .x5 .x0 1)
  execInstrBr s (.SB .x10 .x21 4)

private theorem prelude_code :
    Keygen.instructionAt image 0x12a8 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 0x12ac = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x12b0 = some (.base (.ADDI .x11 .x0 384)) ∧
    Keygen.instructionAt image 0x12b4 = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 0x12b8 = some (.base (.ADDI .x12 .x12 32)) ∧
    Keygen.instructionAt image 0x12bc = some (.base (.ADDI .x5 .x0 1)) ∧
    Keygen.instructionAt image 0x12c0 = some (.base (.SB .x10 .x21 4)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem prelude_steps (s : MachineState) (pc : s.pc = 0x12a8) :
    OrdinarySteps image s 7 (preludeState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 384)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 32)
  let s6 := execInstrBr s5 (.ADDI .x5 .x0 1)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := prelude_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 6
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 5
  · have hp : s1.pc = 0x12ac := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 384)) 4
  · have hp : s2.pc = 0x12b0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 3
  · have hp : s3.pc = 0x12b4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 32)) 2
  · have hp : s4.pc = 0x12b8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x5 .x0 1)) 1
  · have hp : s5.pc = 0x12bc := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 (preludeState s) _ (.base (.SB .x10 .x21 4)) 0
  · have hp : s6.pc = 0x12c0 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,preludeState,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem prelude_fields (s : MachineState) (pc : s.pc = 0x12a8) :
    (preludeState s).pc = 0x12c4 ∧
    (preludeState s).getReg .x5 = 1 ∧
    (preludeState s).getReg .x10 = 0x80000 ∧
    (preludeState s).getReg .x11 = 384 ∧
    (preludeState s).getReg .x12 = 0x80020 ∧
    (preludeState s).getReg .x19 = s.getReg .x19 ∧
    (preludeState s).getReg .x20 = s.getReg .x20 ∧
    (preludeState s).getReg .x21 = s.getReg .x21 := by
  have getReg_setByte (t : MachineState) (a : Word) (b : Byte) (r : Reg) :
      (t.setByte a b).getReg r = t.getReg r := by
    simp [MachineState.setByte]
  simp [preludeState,execInstrBr,getReg_setByte,
    signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem prelude_mem (s : MachineState) (a : Word) :
    (preludeState s).getMem a =
      if a = 0x80000 then
        replaceByte (s.getMem 0x80000) 4 ((s.getReg .x21).truncate 8)
      else s.getMem a := by
  simp [preludeState,execInstrBr,MachineState.setByte,
    alignToDword,byteOffset,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms prelude_steps
#print axioms prelude_mem

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHashPrelude67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67. -/
section
/-! The first WOTS chain hash uses the exact H2 service and its 48-byte query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHashPrelude67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

theorem hash_code :
    Keygen.instructionAt image 0x12c4 = some (.base .ECALL) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem hash_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c4)
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020) :
    Trace hash image s 1 8 1 1
      (writeHash s (hash (hashInput s))) := by
  have fetched : fetch image s = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at,pc] using hash_code
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,source,bits,destination,
      accessValid,rangeValid,MEMORY_BYTES]
  have length : (hashInput s).1 = 384 := by
    simp [hashInput,bits]
  simpa [length,compressions] using
    Trace.hash s _ 0 0 0 0 fetched service valid (Trace.refl _)

theorem hash_call (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12a8) :
    Trace hash image s 8 15 1 1
      (writeHash (preludeState s) (hash (hashInput (preludeState s)))) := by
  obtain ⟨readyPC,service,source,bits,destination,_,_,_⟩ :=
    prelude_fields s pc
  have first : Trace hash image s 7 7 0 0 (preludeState s) :=
    (prelude_steps s pc).trace (hash := hash)
  have second := hash_trace hash (preludeState s) readyPC service source bits destination
  simpa only [Nat.reduceAdd] using first.trans second

theorem first_query (s : MachineState)
    (pc : s.pc = 0x12a8)
    (head : s.getMem 0x80000 = KeygenDomain.header 2 156 0 0 0)
    (step : s.getReg .x21 = 0)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    hashInput (preludeState s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 156 0 0 0) 0 seed) := by
  have field := prelude_fields s pc
  have first : (preludeState s).getMem 0x80000 =
      KeygenDomain.header 2 156 0 0 0 := by
    rw [prelude_mem,if_pos rfl,head,step]
    decide
  have index : ∀ i : Fin 3,
      (preludeState s).getMem (Signing.wordAddress 0x80008 i.val) = 0 := by
    intro i
    rw [prelude_mem,if_neg]
    · exact tree i
    · fin_cases i <;> decide
  have data : ∀ i : Fin 2,
      (preludeState s).getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
    intro i
    rw [prelude_mem,if_neg]
    · exact value i
    · fin_cases i <;> decide
  apply KeygenDomain.query_eq (preludeState s)
    (KeygenDomain.header 2 156 0 0 0) 0 seed
  · exact field.2.2.1
  · exact field.2.2.2.1
  · apply KeygenDomain.words_of_layout (preludeState s)
      (KeygenDomain.header 2 156 0 0 0) 0 seed first
    · intro i
      simpa using index i
    · exact data

#print axioms hash_trace
#print axioms hash_call
#print axioms first_query

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67

end

/-! The top-tree first leaf carries its level, tree address, and seed into H2. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsPrepared67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedKeygenImage67.image

def selectedState (s : MachineState) : MachineState := selectorState (wotsState s)

private theorem x19_index0 (s : MachineState) :
    (GroupedBalancedKeygenFirstHash67.index0State s).getReg .x19 = s.getReg .x19 := by
  simp [GroupedBalancedKeygenFirstHash67.index0State,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem x19_index1 (s : MachineState) :
    (GroupedBalancedKeygenFirstHash67.index1State s).getReg .x19 = s.getReg .x19 := by
  simp [GroupedBalancedKeygenFirstHash67.index1State,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem x19_index2 (s : MachineState) :
    (GroupedBalancedKeygenFirstHash67.index2State s).getReg .x19 = s.getReg .x19 := by
  simp [GroupedBalancedKeygenFirstHash67.index2State,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem x19_header (s : MachineState) :
    (GroupedBalancedKeygenWotsHeader67.headerState s).getReg .x19 = s.getReg .x19 := by
  simp [GroupedBalancedKeygenWotsHeader67.headerState,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem x19_wots (s : MachineState) (pc : s.pc = 0x11d8) :
    (wotsState s).getReg .x19 = s.getReg .x19 := by
  rw [wotsState,GroupedBalancedKeygenWotsIndex67.allState,
    x19_index2,x19_index1,x19_index0,x19_header]
  exact (GroupedBalancedKeygenWotsHeader67.reset_fields s pc).2.2

theorem selected_steps (s : MachineState) (pc : s.pc = 0x11d8)
    (leaf : s.getReg .x19 = 0) :
    OrdinarySteps image s 49 (selectedState s) := by
  have first := wots_steps s pc
  have wpc := wots_pc s pc
  have wx19 : (wotsState s).getReg .x19 = 0 := by
    rw [x19_wots s pc,leaf]
  have second := selector_steps (wotsState s) wpc wx19
  simpa only [selectedState,image,
    GroupedBalancedKeygenWotsPrepared67.image,
    GroupedBalancedKeygenWotsSelector67.image,Nat.reduceAdd] using
      Keygen.ordinary_trans image s (wotsState s)
        (selectedState s) 41 8 first second

theorem selected_layout (s : MachineState)
    (pc : s.pc = 0x11d8) (leaf : s.getReg .x19 = 0)
    (level : s.getMem 0x81000 = 156)
    (chain : s.getMem 0x81030 = 0)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    (selectedState s).pc = 0x12a8 ∧
    (selectedState s).getReg .x21 = 0 ∧
    (selectedState s).getMem 0x80000 = KeygenDomain.header 2 156 0 0 0 ∧
    (∀ i : Fin 3,
      (selectedState s).getMem (Signing.wordAddress 0x80008 i.val) = 0) ∧
    (∀ i : Fin 2,
      (selectedState s).getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) := by
  have wpc := wots_pc s pc
  have wx19 : (wotsState s).getReg .x19 = 0 := by
    rw [x19_wots s pc,leaf]
  have select := selector_fields (wotsState s) wpc wx19
  refine ⟨select.1,select.2.2.1,?_,?_,?_⟩
  · rw [selectedState,selector_mem,wots_header s pc,level,chain]
    decide
  · intro i
    rw [selectedState,selector_mem,wots_index s i]
    exact tree i
  · intro i
    fin_cases i
    · simpa [selectedState,selector_mem,wotsState,all_mem,
        GroupedBalancedKeygenWotsHeader67.header_mem_other,
        GroupedBalancedKeygenWotsHeader67.reset_mem_other,
        Signing.wordAddress] using value 0
    · simpa [selectedState,selector_mem,wotsState,all_mem,
        GroupedBalancedKeygenWotsHeader67.header_mem_other,
        GroupedBalancedKeygenWotsHeader67.reset_mem_other,
        Signing.wordAddress] using value 1

theorem first_input (s : MachineState)
    (pc : s.pc = 0x11d8) (leaf : s.getReg .x19 = 0)
    (level : s.getMem 0x81000 = 156)
    (chain : s.getMem 0x81030 = 0)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    hashInput (GroupedBalancedKeygenWotsHashPrelude67.preludeState (selectedState s)) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 156 0 0 0) 0 seed) := by
  obtain ⟨pc2,step,head,index,data⟩ :=
    selected_layout s pc leaf level chain tree seed value
  exact first_query (selectedState s) pc2 head step index seed data

#print axioms first_input

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67
