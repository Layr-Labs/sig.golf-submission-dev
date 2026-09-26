import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67


/-! The first top-tree WOTS hash runs from the seed-selection state. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

theorem first_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8) (leaf : s.getReg .x19 = 0) :
    Trace hash image s 57 64 1 1
      (writeHash
        (GroupedBalancedKeygenWotsHashPrelude67.preludeState (selectedState s))
        (hash (hashInput
          (GroupedBalancedKeygenWotsHashPrelude67.preludeState (selectedState s))))) := by
  have first : Trace hash image s 49 49 0 0 (selectedState s) :=
    (selected_steps s pc leaf).trace (hash := hash)
  have selectedPC := (GroupedBalancedKeygenWotsSelector67.selector_fields
    (GroupedBalancedKeygenWotsPrepared67.wotsState s)
    (GroupedBalancedKeygenWotsPrepared67.wots_pc s pc)
    (by rw [x19_wots s pc,leaf])).1
  have second := hash_call hash (selectedState s) selectedPC
  simpa only [Nat.reduceAdd] using first.trans second

#print axioms first_trace

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstTrace67


/-! The first H2 answer is the first reference WOTS chain step. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstAnswer67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def readyState (s : MachineState) : MachineState :=
  GroupedBalancedKeygenWotsHashPrelude67.preludeState (selectedState s)

def finalState (hash : Hash) (s : MachineState) : MachineState :=
  writeHash (readyState s) (hash (hashInput (readyState s)))

theorem h2_answer_word (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (i : Fin 4) :
    (writeHash s answer).getMem (Signing.wordAddress 0x80020 i.val) =
      answer.extractLsb' (64*i.val) 64 := by
  fin_cases i <;> simp [writeHash,dst,Signing.wordAddress,
    MachineState.writeWords,Expansion.mem_setMem]

theorem h2_answer_frame (s : MachineState) (answer : BitVec 256)
    (dst : s.getReg .x12 = 0x80020) (a : Word)
    (outside : ∀ i : Fin 4,
      a ≠ Signing.wordAddress 0x80020 i.val) :
    (writeHash s answer).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80020 := outside 0
  have h1 : a ≠ 0x80028 := outside 1
  have h2 : a ≠ 0x80030 := outside 2
  have h3 : a ≠ 0x80038 := outside 3
  simp only [writeHash,MachineState.getMem_setPC,dst,
    MachineState.writeWords,Expansion.mem_setMem]
  change (if a = 0x80038 then _ else if a = 0x80030 then _ else
    if a = 0x80028 then _ else if a = 0x80020 then _ else s.getMem a) =
      s.getMem a
  rw [if_neg h3,if_neg h2,if_neg h1,if_neg h0]

theorem first_answer (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8) (leaf : s.getReg .x19 = 0)
    (level : s.getMem 0x81000 = 156)
    (chain : s.getMem 0x81030 = 0)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (finalState hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (Reference.truncate
          (Reference.query hash 2 156 0 0 0 0 (bytes seed))).extractLsb'
            (64*i.val) 64 := by
  have layout := selected_layout s pc leaf level chain tree seed value
  have destination :=
    (GroupedBalancedKeygenWotsHashPrelude67.prelude_fields
      (selectedState s) layout.1).2.2.2.2.1
  have input := first_input s pc leaf level chain tree seed value
  have query : hash (hashInput (readyState s)) =
      Reference.query hash 2 156 0 0 0 0 (bytes seed) := by
    rw [show hashInput (readyState s) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 156 0 0 0) 0 seed) from input]
    rfl
  intro i
  rw [finalState,h2_answer_word (readyState s)
    (hash (hashInput (readyState s))) destination
    ⟨i.val,by have := i.isLt; omega⟩,query]
  let answer := Reference.query hash 2 156 0 0 0 0 (bytes seed)
  change answer.extractLsb' (64*i.val) 64 =
    (answer.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem first_h2 (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8) (leaf : s.getReg .x19 = 0)
    (level : s.getMem 0x81000 = 156)
    (chain : s.getMem 0x81030 = 0)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) = 0)
    (seed : Reference.Digest)
    (value : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    Trace hash GroupedBalancedKeygenImage67.image s 57 64 1 1
      (finalState hash s) ∧
    (finalState hash s).pc = 0x12c8 ∧
    (∀ i : Fin 2,
      (finalState hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (Reference.truncate
          (Reference.query hash 2 156 0 0 0 0 (bytes seed))).extractLsb'
            (64*i.val) 64) := by
  have pcSelected := (selected_layout s pc leaf level chain tree seed value).1
  have pcReady := (GroupedBalancedKeygenWotsHashPrelude67.prelude_fields
    (selectedState s) pcSelected).1
  refine ⟨?_,?_,first_answer hash s pc leaf level chain tree seed value⟩
  · simpa only [GroupedBalancedKeygenWotsFirstTrace67.image,
      finalState,readyState] using
      GroupedBalancedKeygenWotsFirstTrace67.first_trace hash s pc leaf
  · simp only [finalState,readyState,Keygen.hash_pc,pcReady]
    decide

#print axioms first_answer
#print axioms first_h2

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstAnswer67
