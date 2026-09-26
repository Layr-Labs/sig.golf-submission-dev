import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Semantic67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePrefixSafe67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexPrelude67

/-! The loaded verifier hashes the seed supplied in the bottom wire field. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2LoadedSemantic67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem initial_verify_eq (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) :
    initialState GroupedBalancedProgram67Byte.submission .verify
      (message,pk,wire) =
    initialState program .verify (message,pk,wire) := by
  rfl

theorem loaded_seed_head (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial) :
    ∃ query,
      Trace hash image initial 189 204 1 2 query ∧
      query.pc = 0x1234 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 384 ∧
      query.getMem 0x80000 = KeygenDomain.header 2 0 0 0 0 ∧
      query.getMem 0x80028 ++ query.getMem 0x80020 =
        SignatureEncoding.slice wire 32 16 := by
  have loadedByte : initialState GroupedBalancedProgram67Byte.submission
      .verify (message,pk,wire) = some initial := by
    rw [initial_verify_eq]
    exact loaded
  obtain ⟨otherInitial,_,h5,otherLoaded,h5Run,h5PC,_,pointer⟩ :=
    GroupedBalancedVerifyH5Output67.loaded_output hash (message,pk,wire)
  have initialEq : otherInitial = initial := by
    rw [loadedByte] at otherLoaded
    exact (Option.some.inj otherLoaded).symm
  rw [initialEq] at h5Run
  obtain ⟨safeInitial,safeH5,safeFact⟩ :=
    GroupedBalancedVerifyTreePrefixSafe67.loaded_h5_output_safe
      hash (message,pk,wire)
  have safeLoaded := safeFact.1
  have safeRun := safeFact.2.1
  have low := safeFact.2.2.2.2.2.2
  have safeInitialEq : safeInitial = initial := by
    rw [loadedByte] at safeLoaded
    exact (Option.some.inj safeLoaded).symm
  rw [safeInitialEq] at safeRun low
  have h5Eq : safeH5 = h5 := Trace.deterministic safeRun h5Run
  rw [h5Eq] at low
  let prelude := GroupedBalancedVerifyH2Prelude67.preludeState h5
  have preludeRun := GroupedBalancedVerifyH2Prelude67.prelude_steps
    h5 h5PC pointer
  have preludePC := GroupedBalancedVerifyH2Prelude67.prelude_pc h5 h5PC
  obtain ⟨seedLow,seedHigh,_⟩ :=
    GroupedBalancedVerifyH2Prelude67.prelude_sibling h5 pointer
  obtain ⟨copied,copyRun,copyPC,copyWords,_⟩ :=
    GroupedBalancedVerifyH2InputCopy67.input_copy prelude preludePC
  let query := GroupedBalancedVerifyH2Entry67.setupState copied
  have setupRun := GroupedBalancedVerifyH2Entry67.setup_steps copied copyPC
  have queryPC := GroupedBalancedVerifyH2Entry67.setup_pc copied copyPC
  have prefixRun : Trace hash image initial 189 204 1 2 query := by
    have composed := (h5Run.trans preludeRun.trace).trans
      (copyRun.trace.trans setupRun.trace)
    simpa only [Nat.reduceAdd] using composed
  obtain ⟨copyInitial,safeCopy,copyFact⟩ :=
    GroupedBalancedVerifyTreePrefixSafe67.loaded_h2_copy_safe
      hash (message,pk,wire)
  have safeCopyLoaded := copyFact.1
  have safeCopyRun := copyFact.2.1
  have base := copyFact.2.2.2.2.2.1
  have copyInitialEq : copyInitial = initial := by
    rw [loadedByte] at safeCopyLoaded
    exact (Option.some.inj safeCopyLoaded).symm
  rw [copyInitialEq] at safeCopyRun
  have copiedRun : Trace hash image initial 156 171 1 2 copied := by
    simpa only [Nat.reduceAdd] using
      h5Run.trans (preludeRun.trace.trans copyRun.trace)
  have copiedEq : safeCopy = copied :=
    Trace.deterministic safeCopyRun copiedRun
  rw [copiedEq] at base
  have head := GroupedBalancedVerifyH2Setup67.setup_head copied base
  obtain ⟨_,source,bits,_⟩ := GroupedBalancedVerifyH2Entry67.setup_regs copied
  have initialSeed := GroupedBalancedVerifyLoadedWire67.initial_digest
    message pk wire initial loaded 32 (by decide) (by decide)
  have h5Low : h5.getMem 0x2c720 = initial.getMem 0x2c720 :=
    low 0x2c720 (by decide)
  have h5High : h5.getMem 0x2c728 = initial.getMem 0x2c728 :=
    low 0x2c728 (by decide)
  have copiedLow : copied.getMem 0x80020 = initial.getMem 0x2c720 := by
    calc
      _ = prelude.getMem 0x80510 := by
        simpa [Signing.wordAddress] using copyWords 0
      _ = h5.getMem 0x2c720 := seedLow
      _ = initial.getMem 0x2c720 := h5Low
  have copiedHigh : copied.getMem 0x80028 = initial.getMem 0x2c728 := by
    calc
      _ = prelude.getMem 0x80518 := by
        simpa [Signing.wordAddress] using copyWords 1
      _ = h5.getMem 0x2c728 := seedHigh
      _ = initial.getMem 0x2c728 := h5High
  have queryLow : query.getMem 0x80020 = copied.getMem 0x80020 := by
    simpa [query,Signing.wordAddress] using
      (GroupedBalancedVerifyH2Setup67.setup_seed_words copied 0)
  have queryHigh : query.getMem 0x80028 = copied.getMem 0x80028 := by
    simpa [query,Signing.wordAddress] using
      (GroupedBalancedVerifyH2Setup67.setup_seed_words copied 1)
  refine ⟨query,prefixRun,queryPC,source,bits,head,?_⟩
  rw [queryHigh,queryLow,copiedHigh,copiedLow]
  simpa only [show BitVec.ofNat 64 (0x2c700+32+8) = (0x2c728 : Word) by decide,
    show BitVec.ofNat 64 (0x2c700+32) = (0x2c720 : Word) by decide]
    using initialSeed

private theorem input_setup_code : Keygen.CopySetupCode image
    0x1184 0x510 0x20 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem input_copy_code : Keygen.CopyCode image 0x1198 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem loaded_index_input (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ query,
      Trace hash image initial 189 204 1 2 query ∧
      query.pc = 0x1234 ∧
      ((query.getMem 0x80018 ++ query.getMem 0x80010 ++
        query.getMem 0x80008) : BitVec 192).toNat =
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat ∧
      ((query.getMem 0x81018 ++ query.getMem 0x81010 ++
        query.getMem 0x81008) : BitVec 192).toNat =
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat := by
  obtain ⟨prelude,preludeRun,preludePC,_,preludeIndex⟩ :=
    GroupedBalancedVerifyIndexPrelude67.loaded_prelude_index
      hash message pk wire initial loaded pc
  obtain ⟨copied,copyRun,copyPC,_,_⟩ :=
    GroupedBalancedVerifyH2InputCopy67.input_copy prelude preludePC
  obtain ⟨other,otherRun,_,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1184 0x510 0x20 0x80510 0x80020
      input_setup_code input_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      prelude preludePC
  have copiedEq : copied = other :=
    Keygen.ordinary_deterministic copyRun otherRun
  have copiedIndex : ∀ i : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 i.val) =
        prelude.getMem (Signing.wordAddress 0x81008 i.val) := by
    intro i
    rw [copiedEq]
    exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)
  let query := GroupedBalancedVerifyH2Entry67.setupState copied
  have setupRun := GroupedBalancedVerifyH2Entry67.setup_steps copied copyPC
  have queryRun : Trace hash image initial 189 204 1 2 query := by
    simpa only [Nat.reduceAdd] using
      preludeRun.trans (copyRun.trace.trans setupRun.trace)
  have queryIndex : ∀ i : Fin 3,
      query.getMem (Signing.wordAddress 0x80008 i.val) =
        prelude.getMem (Signing.wordAddress 0x81008 i.val) := by
    intro i
    exact (GroupedBalancedVerifyH2Setup67.setup_index_words copied i).trans
      (copiedIndex i)
  have scratchIndex : ∀ i : Fin 3,
      query.getMem (Signing.wordAddress 0x81008 i.val) =
        prelude.getMem (Signing.wordAddress 0x81008 i.val) := by
    intro i
    exact (GroupedBalancedVerifyH2Setup67.setup_index_frame copied i).trans
      (copiedIndex i)
  have low : query.getMem 0x80008 = prelude.getMem 0x81008 := by
    simpa [Signing.wordAddress] using queryIndex 0
  have mid : query.getMem 0x80010 = prelude.getMem 0x81010 := by
    simpa [Signing.wordAddress] using queryIndex 1
  have high : query.getMem 0x80018 = prelude.getMem 0x81018 := by
    simpa [Signing.wordAddress] using queryIndex 2
  have scratchLow : query.getMem 0x81008 = prelude.getMem 0x81008 := by
    simpa [Signing.wordAddress] using scratchIndex 0
  have scratchMid : query.getMem 0x81010 = prelude.getMem 0x81010 := by
    simpa [Signing.wordAddress] using scratchIndex 1
  have scratchHigh : query.getMem 0x81018 = prelude.getMem 0x81018 := by
    simpa [Signing.wordAddress] using scratchIndex 2
  refine ⟨query,queryRun,
    GroupedBalancedVerifyH2Entry67.setup_pc copied copyPC,?_,?_⟩
  · rw [high,mid,low]
    exact preludeIndex
  · rw [scratchHigh,scratchMid,scratchLow]
    exact preludeIndex

theorem loaded_query_refines (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ query,
      Trace hash image initial 189 204 1 2 query ∧
      query.pc = 0x1234 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 384 ∧
      query.getReg .x12 = 0x80300 ∧
      hashInput query = SecurityRandomOracle.addressedInput
        2 0
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat
        0 0 0 (bytes (SignatureEncoding.slice wire 32 16)) ∧
      ((query.getMem 0x81018 ++ query.getMem 0x81010 ++
        query.getMem 0x81008) : BitVec 192).toNat =
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat := by
  obtain ⟨seedQuery,seedRun,seedPC,source,bits,head,seedPair⟩ :=
    loaded_seed_head hash message pk wire initial loaded
  obtain ⟨indexQuery,indexRun,_,packed,scratch⟩ :=
    loaded_index_input hash message pk wire initial loaded pc
  have same : indexQuery = seedQuery :=
    Trace.deterministic indexRun seedRun
  rw [same] at packed scratch
  let index := Reference.indexOf hash message
    (GroupedBalancedWire67.decode wire).randomizer
  let seed := SignatureEncoding.slice wire 32 16
  have indexWords := GroupedBalancedVerifyH2Semantic67.index_words_of_packed
    seedQuery index.toNat packed
  have seedWords := GroupedBalancedVerifyH2Semantic67.seed_words_of_pair
    seedQuery seed seedPair
  have inputEq := GroupedBalancedVerifyH2Semantic67.query_eq seedQuery
    index.toNat seed source bits head indexWords seedWords
  obtain ⟨officialInitial,officialQuery,officialLoaded,officialRun,_,
    officialService,_,_,officialDest,_⟩ :=
    GroupedBalancedVerifyH2Loaded67.loaded_query hash (message,pk,wire)
  have officialLoadedAtInitial : initialState GroupedBalancedProgram67Byte.submission
      .verify (message,pk,wire) = some initial := by
    rw [initial_verify_eq]
    exact loaded
  have sameInitial : officialInitial = initial := by
    rw [officialLoadedAtInitial] at officialLoaded
    exact (Option.some.inj officialLoaded).symm
  rw [sameInitial] at officialRun
  have querySame : officialQuery = seedQuery :=
    Trace.deterministic officialRun seedRun
  rw [querySame] at officialService officialDest
  refine ⟨seedQuery,seedRun,seedPC,officialService,source,bits,
    officialDest,inputEq,scratch⟩

private theorem hash_code : Keygen.instructionAt image 0x1234 =
    some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem output_setup_code : Keygen.CopySetupCode image
    0x1238 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem output_copy_code : Keygen.CopyCode image 0x124c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem loaded_leaf_answer (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ final,
      Trace hash image initial 207 229 2 3 final ∧
      final.pc = 0x1264 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (GroupedBottomTree.leafFromSeed hash
            (Reference.indexOf hash message
              (GroupedBalancedWire67.decode wire).randomizer).toNat
            (SignatureEncoding.slice wire 32 16)).extractLsb'
              (64*i.val) 64) ∧
      ((final.getMem 0x81018 ++ final.getMem 0x81010 ++
        final.getMem 0x81008) : BitVec 192).toNat =
        (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer).toNat := by
  obtain ⟨query,prefixRun,queryPC,service,source,bits,dest,queryInput,
    queryIndex⟩ :=
    loaded_query_refines hash message pk wire initial loaded pc
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 384 source (by simpa using bits)
      dest (by decide)
  have hlen : (hashInput query).1 = 384 := by
    simp [hashInput,bits,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 1 := by
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 8 1 1 afterHash := by
    have fetched : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,queryPC] using hash_code
    have raw := Trace.hash query afterHash 0 0 0 0 fetched service valid
      (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1238 := by
    simpa [afterHash,answer,Keygen.hash_pc,queryPC] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,words,_,_,frame⟩ :=
    Keygen.copy_two image 0x1238 0x300 0x500 0x80300 0x80500
      output_setup_code output_copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      afterHash afterPC
  have stored : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80500 i.val) =
        (hash (hashInput query)).extractLsb' (64*i.val) 64 := by
    intro i
    have result := Signing.hash_answer_word query answer dest
      (⟨i.val,by have h := i.isLt; omega⟩ : Fin 4)
    exact (words i).trans (by simpa [afterHash,answer] using result)
  have scratchFrame : ∀ i : Fin 3,
      final.getMem (Signing.wordAddress 0x81008 i.val) =
        query.getMem (Signing.wordAddress 0x81008 i.val) := by
    intro i
    have after : afterHash.getMem
        (Signing.wordAddress 0x81008 i.val) =
        query.getMem (Signing.wordAddress 0x81008 i.val) :=
      Signing.hash_answer_frame query answer dest _
        (by intro j; fin_cases i <;> fin_cases j <;> decide)
    exact (frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)).trans
      after
  have low : final.getMem 0x81008 = query.getMem 0x81008 := by
    simpa [Signing.wordAddress] using scratchFrame 0
  have mid : final.getMem 0x81010 = query.getMem 0x81010 := by
    simpa [Signing.wordAddress] using scratchFrame 1
  have high : final.getMem 0x81018 = query.getMem 0x81018 := by
    simpa [Signing.wordAddress] using scratchFrame 2
  refine ⟨final,?_,by simpa using finalPC,?_,?_⟩
  · have composed := prefixRun.trans (hashRun.trans copyRun.trace)
    simpa only [Nat.reduceAdd] using composed
  · exact GroupedBalancedVerifyH2Semantic67.answer_words hash query final
      _ _ queryInput stored
  · rw [high,mid,low]
    exact queryIndex

#print axioms initial_verify_eq
#print axioms loaded_seed_head
#print axioms loaded_index_input
#print axioms loaded_query_refines
#print axioms loaded_leaf_answer
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2LoadedSemantic67
