import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTick67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsTickLoop67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixData67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsGenericAnswer67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalTick67. -/
section
/-! Parametric WOTS tick semantics for the direct67 keygen image. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsGenericAnswer67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsTick67
open GroupedBalancedKeygenWotsHashPrelude67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem tick_query (s : MachineState)
    (level tree leaf chain step : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 level leaf chain step)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    hashInput (storeState s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 level leaf chain step) tree value) := by
  obtain ⟨_, regs⟩ := store_fields s pc
  have first : (storeState s).getMem 0x80000 =
      KeygenDomain.header 2 level leaf chain step := by
    rw [store_mem s source 0x80000, if_pos rfl, header]
  have index : ∀ i : Fin 3,
      (storeState s).getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [store_mem s source, if_neg]
    · exact treeWords i
    · fin_cases i <;> decide
  have data : ∀ i : Fin 2,
      (storeState s).getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [store_mem s source, if_neg]
    · exact valueWords i
    · fin_cases i <;> decide
  apply KeygenDomain.query_eq (storeState s)
    (KeygenDomain.header 2 level leaf chain step) tree value
  · exact (regs .x10).trans source
  · exact (regs .x11).trans bits
  · exact KeygenDomain.words_of_layout (storeState s)
      (KeygenDomain.header 2 level leaf chain step) tree value
      first index data

theorem tick_answer (hash : Hash) (s : MachineState)
    (level tree leaf chain step : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 level leaf chain step)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (storeState s) (hash (hashInput (storeState s)))).getMem
        (Signing.wordAddress 0x80020 i.val) =
        (Reference.truncate
          (Reference.query hash 2 level tree leaf chain step
            (bytes value))).extractLsb' (64*i.val) 64 := by
  have input := tick_query s level tree leaf chain step value pc source
    bits header treeWords valueWords
  have query : hash (hashInput (storeState s)) =
      Reference.query hash 2 level tree leaf chain step (bytes value) := by
    rw [input]
    rfl
  have dst := (store_fields s pc).2 .x12 |>.trans destination
  intro i
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_word
    (storeState s) (hash (hashInput (storeState s))) dst
    ⟨i.val, by have := i.isLt; omega⟩, query]
  let answer := Reference.query hash 2 level tree leaf chain step
    (bytes value)
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem first_query (s : MachineState)
    (level tree chain : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x12a8)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 level 0 chain 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    hashInput (preludeState s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 level 0 chain 0) tree value) := by
  have field := prelude_fields s pc
  have first : (preludeState s).getMem 0x80000 =
      KeygenDomain.header 2 level 0 chain 0 := by
    rw [prelude_mem, if_pos rfl, header]
  have index : ∀ i : Fin 3,
      (preludeState s).getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [prelude_mem, if_neg]
    · exact treeWords i
    · fin_cases i <;> decide
  have data : ∀ i : Fin 2,
      (preludeState s).getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [prelude_mem, if_neg]
    · exact valueWords i
    · fin_cases i <;> decide
  apply KeygenDomain.query_eq (preludeState s)
    (KeygenDomain.header 2 level 0 chain 0) tree value
  · exact field.2.2.1
  · exact field.2.2.2.1
  · exact KeygenDomain.words_of_layout (preludeState s)
      (KeygenDomain.header 2 level 0 chain 0) tree value
      first index data

theorem first_answer (hash : Hash) (s : MachineState)
    (level tree chain : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x12a8)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 level 0 chain 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (preludeState s) (hash (hashInput (preludeState s)))).getMem
        (Signing.wordAddress 0x80020 i.val) =
        (Reference.truncate
          (Reference.query hash 2 level tree 0 chain 0
            (bytes value))).extractLsb' (64*i.val) 64 := by
  have input := first_query s level tree chain value pc header
    treeWords valueWords
  have query : hash (hashInput (preludeState s)) =
      Reference.query hash 2 level tree 0 chain 0 (bytes value) := by
    rw [input]
    rfl
  have destination := (prelude_fields s pc).2.2.2.2.1
  intro i
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_word
    (preludeState s) (hash (hashInput (preludeState s))) destination
    ⟨i.val, by have := i.isLt; omega⟩, query]
  let answer := Reference.query hash 2 level tree 0 chain 0
    (bytes value)
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

#print axioms tick_query
#print axioms tick_answer
#print axioms first_query
#print axioms first_answer
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsGenericAnswer67

end

/-! One actual direct67 keygen H2 tick computes the next WOTS value. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenWotsTickLoop67
open GroupedBalancedKeygenWotsTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem tick_value (hash : Hash) (s : MachineState)
    (base tree chain step : Nat) (value : Reference.Digest)
    (bound : chain < 67)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain step)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (tickNext hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base tree
          ⟨chain,bound⟩ step value).extractLsb' (64*i.val) 64 := by
  intro i
  rw [tickNext,GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
  have result := GroupedBalancedKeygenWotsGenericAnswer67.tick_answer
    hash s base tree 0 chain step value pc source bits destination
      header treeWords valueWords i
  simpa only [GroupedBalancedUpperTree67.chainHash] using result

theorem tick_header (hash : Hash) (s : MachineState)
    (base chain step : Nat)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain step) :
    (tickNext hash s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain step := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext,GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst 0x80000
    (by intro i; fin_cases i <;> decide)]
  rw [store_mem s source 0x80000,if_pos rfl]
  exact header

theorem tick_tree (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x12c0)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (i : Fin 3) :
    (tickNext hash s).getMem
      (Signing.wordAddress 0x80008 i.val) =
        s.getMem (Signing.wordAddress 0x80008 i.val) := by
  have dst : (storeState s).getReg .x12 = 0x80020 :=
    ((store_fields s pc).2 .x12).trans destination
  rw [tickNext,GroupedBalancedKeygenWotsLoopAdvance67.advance_mem]
  rw [GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame
    (storeState s) (hash (hashInput (storeState s))) dst _
    (by intro j; fin_cases i <;> fin_cases j <;> decide)]
  rw [store_mem s source,if_neg (by fin_cases i <;> decide)]

structure LoopData (s : MachineState) (base tree : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (step maxStep : Nat) (value : Reference.Digest) : Prop where
  pc : s.pc = 0x12c0
  stepReg : s.getReg .x21 = BitVec.ofNat 64 step
  maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep
  service : s.getReg .x5 = 1
  source : s.getReg .x10 = 0x80000
  bits : s.getReg .x11 = 384
  destination : s.getReg .x12 = 0x80020
  headerCarry : ∃ old, old < 11 ∧
    s.getMem 0x80000 = KeygenDomain.header 2 base 0 chain.val old
  treeWords : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x80008 i.val) =
      (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64
  valueWords : ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x80020 i.val) =
      value.extractLsb' (64*i.val) 64

theorem step_data (hash : Hash) (s : MachineState)
    (base tree : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (step maxStep : Nat) (value : Reference.Digest)
    (baseBound : base < 256) (stepBound : step < maxStep)
    (maxBound : maxStep ≤ 10)
    (data : LoopData s base tree chain step maxStep value) :
    let next := tickNext hash s
    Trace hash GroupedBalancedKeygenImage67.image s 4 11 1 1 next ∧
    next.pc =
      (if step + 1 = maxStep then 0x12d0 else 0x12c0) ∧
    next.getReg .x21 = BitVec.ofNat 64 (step+1) ∧
    next.getReg .x20 = BitVec.ofNat 64 maxStep ∧
    (∀ r : Reg, r ≠ .x21 → next.getReg r = s.getReg r) ∧
    next.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val step ∧
    (∀ i : Fin 3,
      next.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64) ∧
    (∀ i : Fin 2,
      next.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base tree chain step value).extractLsb'
          (64*i.val) 64) := by
  obtain ⟨old,oldBound,oldHeader⟩ := data.headerCarry
  have stagedHeader : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val step := by
    rw [oldHeader,data.stepReg]
    have trunc : (BitVec.ofNat 64 step).truncate 8 =
        BitVec.ofNat 8 step := by simp
    rw [trunc]
    exact GroupedBalancedByteFastSuffixData67.header_step_replace
      base chain.val old step baseBound
      (by have := chain.isLt; omega) (by omega) (by omega)
  have first := tick_next_trace hash s data.pc data.service data.source
    data.bits data.destination
  have fields := tick_next_fields hash s data.pc
  have succWord : (BitVec.ofNat 64 step : Word) + 1 =
      BitVec.ofNat 64 (step+1) := by simp [BitVec.ofNat_add]
  refine ⟨first,?_,?_,?_,fields.2.2.2,?_,?_,?_⟩
  · rw [fields.1,data.stepReg,data.maxReg,succWord]
    by_cases eq : step+1 = maxStep
    · rw [if_pos eq,if_neg]
      intro different
      exact different (congrArg (BitVec.ofNat 64) eq)
    · rw [if_neg eq,if_pos]
      intro same
      have h := congrArg BitVec.toNat same
      simp [BitVec.toNat_ofNat] at h
      omega
  · rw [fields.2.1,data.stepReg,succWord]
  · rw [fields.2.2.1,data.maxReg]
  · exact tick_header hash s base chain.val step data.pc data.source
      data.destination stagedHeader
  · intro i
    rw [tick_tree hash s data.pc data.source data.destination i]
    exact data.treeWords i
  · exact tick_value hash s base tree chain.val step value chain.isLt
      data.pc data.source data.bits data.destination stagedHeader
      data.treeWords data.valueWords

theorem run_data (hash : Hash) (base tree : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (remaining : Nat) (s : MachineState) (start : Nat)
    (value : Reference.Digest)
    (baseBound : base < 256) (positive : 0 < remaining)
    (maxBound : start + remaining ≤ 10)
    (data : LoopData s base tree chain start (start+remaining) value) :
    ∃ final,
      Trace hash GroupedBalancedKeygenImage67.image s
        (4*remaining) (11*remaining) remaining remaining final ∧
      final.pc = 0x12d0 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            start remaining value).extractLsb' (64*i.val) 64) := by
  induction remaining generalizing s start value with
  | zero => omega
  | succ remaining ih =>
      let next := tickNext hash s
      have stepBound : start < start + (remaining+1) := by omega
      have step := step_data hash s base tree chain start
        (start+(remaining+1)) value baseBound stepBound
        (by simpa only [Nat.add_assoc] using maxBound) data
      rcases step with ⟨first,nextPC,nextStep,nextMax,reg,
        nextHeader,nextTree,nextValue⟩
      by_cases last : remaining = 0
      · subst remaining
        have done : next.pc = 0x12d0 := by
          rw [nextPC]
          simp
        refine ⟨next,?_,done,?_⟩
        · simpa only [Nat.mul_one] using first
        · intro i
          simpa only [walk] using nextValue i
      · have left : 0 < remaining := by omega
        have nextPC' : next.pc = 0x12c0 := by
          rw [nextPC]
          have neq : start+1 ≠ start+(remaining+1) := by omega
          exact if_neg neq
        have nextData : LoopData next base tree chain
            (start+1) ((start+1)+remaining)
            (GroupedBalancedUpperTree67.chainHash hash base tree
              chain start value) := by
          refine ⟨nextPC',nextStep,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · simpa only [Nat.add_assoc,Nat.add_comm remaining 1] using nextMax
          · exact (reg .x5 (by decide)).trans data.service
          · exact (reg .x10 (by decide)).trans data.source
          · exact (reg .x11 (by decide)).trans data.bits
          · exact (reg .x12 (by decide)).trans data.destination
          · exact ⟨start,by omega,nextHeader⟩
          · exact nextTree
          · exact nextValue
        obtain ⟨final,rest,done,result⟩ :=
          ih next (start+1)
            (GroupedBalancedUpperTree67.chainHash hash base tree
              chain start value)
            left (by omega) nextData
        refine ⟨final,?_,done,?_⟩
        · simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,
            Nat.add_left_comm] using first.trans rest
        · intro i
          simpa only [walk] using result i

#print axioms tick_value
#print axioms tick_header
#print axioms tick_tree
#print axioms step_data
#print axioms run_data

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalTick67
