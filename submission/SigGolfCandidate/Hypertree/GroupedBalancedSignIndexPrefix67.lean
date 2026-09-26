import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexQuery67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerLoaded67
import SigGolfCandidate.Hypertree.SignExecutionSetup

/-! The actual signer entry performs the tag6 and tag5 calls in order. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrefix67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

theorem index_prefix (hash : Hash) (s : MachineState)
    (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x10d8)
    (hmessage : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8)
    (hr : ∀ i, i < 32 → s.getByte
      (BitVec.ofNat 64 (0x20060+i)) = r.extractLsb' (8*i) 8) :
    ∃ ready after,
      Trace hash image s 88 103 1 2 after ∧
      ready.pc = 0x11a4 ∧ after.pc = 0x11a8 ∧
      hashInput ready = SecurityRandomOracle.indexInput message r ∧
      after = writeHash ready (hash (SecurityRandomOracle.indexInput message r)) ∧
      (∀ i : Fin 4,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (hash (SecurityRandomOracle.indexInput message r)).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 4, after.getMem (Signing.wordAddress 0x20 i.val) =
        s.getMem (Signing.wordAddress 0x20 i.val)) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → after.getMem a = s.getMem a) ∧
      (∀ a : Word, 0x20060 ≤ a.toNat → a.toNat < 0x20080 →
        after.getMem a = s.getMem a) := by
  obtain ⟨prepared,pre,preparedPC,words,prepareFrame⟩ :=
    GroupedBalancedSignIndexPrepare67.index_prepare s pc
  let ready := GroupedBalancedSignIndexHash67.indexHashState prepared
  have query := GroupedBalancedSignIndexQuery67.index_query
    s prepared message r hmessage hr words
  have call := GroupedBalancedSignIndexQuery67.index_hash_call
    hash prepared preparedPC
  have readyPC : ready.pc = 0x11a4 := by
    simp [ready,GroupedBalancedSignIndexHash67.indexHashState_pc,
      preparedPC]
  let after := writeHash ready (hash (SecurityRandomOracle.indexInput message r))
  have afterEq : after = writeHash ready (hash (hashInput ready)) := by
    rw [query]
  refine ⟨ready,after,?_,readyPC,?_,query,rfl,?_,?_,?_,?_⟩
  · rw [afterEq]
    exact pre.trace.trans call
  · simp [after,Keygen.hash_pc,readyPC]
  · intro i
    change (writeHash ready
      (hash (SecurityRandomOracle.indexInput message r))).getMem
        (Signing.wordAddress 0x80300 i.val) = _
    rw [←query]
    exact Signing.hash_answer_word ready (hash (hashInput ready))
      (GroupedBalancedSignIndexHash67.indexHashState_regs prepared).2.2.2 i
  · intro i
    rw [Signing.hash_answer_frame ready _
      (GroupedBalancedSignIndexHash67.indexHashState_regs prepared).2.2.2
      (Signing.wordAddress 0x20 i.val)
      (by intro j; fin_cases i <;> fin_cases j <;> decide)]
    have readyMem : ready.getMem (Signing.wordAddress 0x20 i.val) =
        prepared.getMem (Signing.wordAddress 0x20 i.val) := by
      simp [ready,GroupedBalancedSignIndexHash67.indexHashState,execInstrBr]
    rw [readyMem]
    exact prepareFrame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)
  · intro a high
    have hashOutside : ∀ i : Fin 4,
        a ≠ Signing.wordAddress 0x80300 i.val := by
      intro i
      have ne := Signing.outside_copy_word a.toNat 0x80300 4 i.val
        a.isLt (by decide) i.isLt (Or.inr (by omega))
      simpa using ne
    rw [Signing.hash_answer_frame ready _
      (GroupedBalancedSignIndexHash67.indexHashState_regs prepared).2.2.2
      a hashOutside]
    have readyMem : ready.getMem a = prepared.getMem a := by
      simp [ready,GroupedBalancedSignIndexHash67.indexHashState,execInstrBr]
    rw [readyMem]
    apply prepareFrame
    intro i
    have ne := Signing.outside_copy_word a.toNat 0x80000 14 i.val
      a.isLt (by decide) i.isLt (Or.inr (by omega))
    simpa using ne
  · intro a low high
    have hashOutside : ∀ i : Fin 4,
        a ≠ Signing.wordAddress 0x80300 i.val := by
      intro i
      have ne := Signing.outside_copy_word a.toNat 0x80300 4 i.val
        a.isLt (by decide) i.isLt (Or.inl (by omega))
      simpa using ne
    rw [Signing.hash_answer_frame ready _
      (GroupedBalancedSignIndexHash67.indexHashState_regs prepared).2.2.2
      a hashOutside]
    have readyMem : ready.getMem a = prepared.getMem a := by
      simp [ready,GroupedBalancedSignIndexHash67.indexHashState,execInstrBr]
    rw [readyMem]
    apply prepareFrame
    intro i
    have ne := Signing.outside_copy_word a.toNat 0x80000 14 i.val
      a.isLt (by decide) i.isLt (Or.inl (by omega))
    simpa using ne

theorem loaded_two_hash_prefix (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial randomized ready after,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial 196 226 2 4 after ∧
      randomized.pc = 0x10d8 ∧ ready.pc = 0x11a4 ∧ after.pc = 0x11a8 ∧
      readBuffer randomized 0x20060 32 =
        Reference.randomizer hash secretKey message ∧
      hashInput ready = SecurityRandomOracle.indexInput message
        (Reference.randomizer hash secretKey message) ∧
      after = writeHash ready
        (hash (SecurityRandomOracle.indexInput message
          (Reference.randomizer hash secretKey message))) ∧
      (∀ i : Fin 4,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (hash (SecurityRandomOracle.indexInput message
            (Reference.randomizer hash secretKey message))).extractLsb'
              (64*i.val) 64) ∧
      (∀ i : Fin 4, after.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → after.getMem a = initial.getMem a) ∧
      (∀ i : Fin 4,
        after.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨initial,loaded,pc⟩ :=
    initialState_exists submission GroupedBalancedProgram67Byte.admissible
      .sign (secretKey,cache,message)
  have sk := Loader.sign_secretKey submission
    (GroupedBalancedProgram67Byte.admissible.2 .sign) (by rfl)
    secretKey cache message initial loaded
  have msg := Loader.sign_message submission
    (GroupedBalancedProgram67Byte.admissible.2 .sign) (by rfl)
    secretKey cache message initial loaded
  obtain ⟨randomized,first,randomPC,randomWords,lowFrame,randomHigh⟩ :=
    GroupedBalancedSignRandomizerLoaded67.entry_randomizer_low_frame
      hash initial secretKey message pc sk msg
  have messageBytes : ∀ i, i < 32 → randomized.getByte
      (BitVec.ofNat 64 i) = message.extractLsb' (8*i) 8 := by
    intro i hi
    have eq := Signing.low_words_byte initial randomized lowFrame 0 i
      (by decide) (by omega)
    simpa only [Nat.zero_add] using
      (show randomized.getByte (BitVec.ofNat 64 i) =
        initial.getByte (BitVec.ofNat 64 i) from by
          simpa only [Nat.zero_add] using eq).trans (msg i hi)
  have randomizerBytes : ∀ i, i < 32 → randomized.getByte
      (BitVec.ofNat 64 (0x20060+i)) =
        (Reference.randomizer hash secretKey message).extractLsb'
          (8*i) 8 := by
    exact Signing.bytes_of_answer_words randomized 0x20060
      (Reference.randomizer hash secretKey message)
      (by decide) (by decide) randomWords
  obtain ⟨ready,after,second,readyPC,afterPC,query,answer,answerWords,keyFrame,
    secondHigh,randomFrame⟩ :=
    index_prefix hash randomized message
      (Reference.randomizer hash secretKey message)
      randomPC messageBytes randomizerBytes
  have output : readBuffer randomized 0x20060 32 =
      Reference.randomizer hash secretKey message := by
    apply Memory.readBuffer_of_bytes
    exact randomizerBytes
  have keyOut : ∀ i : Fin 4,
      after.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [keyFrame i,lowFrame _ (by fin_cases i <;> decide)]
    exact Signing.secretKey_words_of_bytes initial 0x20 secretKey
      (by decide) (by decide) sk i
  have highOut : ∀ a : Word, 0xfff700 ≤ a.toNat →
      after.getMem a = initial.getMem a := by
    intro a high
    exact (secondHigh a high).trans (randomHigh a high)
  refine ⟨initial,randomized,ready,after,loaded,?_,randomPC,
    readyPC,afterPC,output,query,answer,answerWords,keyOut,highOut,?_⟩
  simpa only [Nat.reduceAdd] using first.trans second
  intro i
  rw [randomFrame _ (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)]
  exact randomWords i

#print axioms loaded_two_hash_prefix

end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrefix67
