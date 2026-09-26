import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizerStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtract67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoopStart67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomIndexBounds67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH167
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSetupStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafStack67


/-! The official signer prefix keeps the initial stack pointer through both hashes. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignPrefixStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

theorem prefix_sp (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1000)
    (trace : Trace hash image s 196 226 2 4 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨_,randomized,first,randomPc,_,_⟩ :=
    GroupedBalancedSignPrepare67.entry_randomizer_trace hash s pc
  obtain ⟨after,second⟩ :=
    GroupedBalancedSignIndexStack67.index_trace hash randomized randomPc
  have constructed : Trace hash image s 196 226 2 4 after := by
    simpa [GroupedBalancedSignPrepare67.image,image] using first.trans second
  have same := Trace.deterministic trace constructed
  rw [same]
  exact (GroupedBalancedSignIndexStack67.index_sp hash randomized after
    randomPc second).trans
    (GroupedBalancedSignRandomizerStack67.entry_sp hash s randomized pc first)

theorem loaded_stack_base (program : Submission) (admitted : program.Admissible)
    (secretKey : SecretKey) (cache : Cache) (message : Message)
    (s : MachineState)
    (loaded : initialState program .sign (secretKey,cache,message) = some s) :
    s.getReg .x2 = BitVec.ofNat 64 (Riscv.dataBase (program.image .sign)) := by
  unfold initialState at loaded
  rw [if_pos (admitted.2 .sign)] at loaded
  cases Option.some.inj loaded
  exact MachineState.getReg_setReg_eq (by decide)

theorem loaded_stack (secretKey : SecretKey) (cache : Cache)
    (message : Message) (s : MachineState)
    (loaded : initialState submission .sign (secretKey,cache,message) = some s) :
    s.getReg .x2 = 0xfff700 := by
  have dataBase : Riscv.dataBase GroupedBalancedSignImage67.image = 0xfff700 := by
    simp [Riscv.dataBase,GroupedBalancedSignImage67.image,
      GroupedBalancedDecoderByte67.data_length,MEMORY_BYTES]
  have h := loaded_stack_base submission GroupedBalancedProgram67Byte.admissible
    secretKey cache message s loaded
  change s.getReg .x2 = BitVec.ofNat 64 0xfff700
  rw [←dataBase]
  exact h

theorem loaded_pc (secretKey : SecretKey) (cache : Cache)
    (message : Message) (s : MachineState)
    (loaded : initialState submission .sign (secretKey,cache,message) = some s) :
    s.pc = 0x1000 := by
  obtain ⟨other,otherLoaded,otherPc⟩ :=
    initialState_exists submission GroupedBalancedProgram67Byte.admissible
      .sign (secretKey,cache,message)
  rw [loaded] at otherLoaded
  exact (Option.some.inj otherLoaded).symm ▸ otherPc

#print axioms prefix_sp
#print axioms loaded_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignPrefixStack67



namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtractStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem copy_sp (s final : MachineState) (pc : s.pc = 0x11a8)
    (trace : OrdinarySteps image s 17 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignIndexExtract67.setupState s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x11bc
    GroupedBalancedSignIndexExtract67.copy_code 0x80300 0x81090 2 begun
    (GroupedBalancedSignIndexExtract67.copy_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignIndexExtract67.setup_steps s pc
  have constructed : OrdinarySteps image s 17 other := by
    simpa only [show 5+12=17 by decide] using
      Keygen.ordinary_trans image s begun other 5 12 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignIndexExtract67.setupState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem extract_sp (s final : MachineState) (pc : s.pc = 0x11a8)
    (trace : OrdinarySteps image s 25 final) :
    final.getReg .x2 = s.getReg .x2 := by
  obtain ⟨copied,copyTrace,copyPc,_,_⟩ :=
    GroupedBalancedSignIndexExtract67.copy_low s pc
  let stored := GroupedBalancedSignIndexExtract67.storeState copied
  have storeTrace := GroupedBalancedSignIndexExtract67.store_steps copied copyPc
  have constructed : OrdinarySteps image s 25 stored := by
    simpa only [show 17+8=25 by decide] using
      Keygen.ordinary_trans image s copied stored 17 8 copyTrace storeTrace
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same]
  have storedSp : stored.getReg .x2 = copied.getReg .x2 := by
    simp [stored,GroupedBalancedSignIndexExtract67.storeState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact storedSp.trans (copy_sp s copied pc copyTrace)

#print axioms extract_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtractStack67


/-! From official loaded signer state through all 1,024 bottom leaves. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

private theorem stable_control (a : Word)
    (h : a = 0x81060 ∨ a = 0x810d0 ∨ a = 0x810f8 ∨
      a = 0x810e8 ∨ a = 0x81090) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress a := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress
    simp [Signing.wordAddress]
    constructor <;> intro i <;> fin_cases i <;> decide

private theorem stable_rounded (i : Fin 3) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress
      (Signing.wordAddress 0x810a8 i.val) := by
  fin_cases i <;>
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress <;>
    simp [Signing.wordAddress] <;>
    constructor <;> intro j <;> fin_cases j <;> decide

private theorem stable_index (i : Fin 3) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress
      (Signing.wordAddress 0x81090 i.val) := by
  fin_cases i <;>
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress <;>
    simp [Signing.wordAddress] <;>
    constructor <;> intro j <;> fin_cases j <;> decide

private theorem stable_key (i : Fin 4) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress
      (Signing.wordAddress 0x20 i.val) := by
  fin_cases i <;>
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress <;>
    simp [Signing.wordAddress] <;>
    constructor <;> intro j <;> fin_cases j <;> decide

private theorem stable_randomizer (i : Fin 4) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress
      (Signing.wordAddress 0x20060 i.val) := by
  fin_cases i <;>
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress <;>
    simp [Signing.wordAddress] <;>
    constructor <;> intro j <;> fin_cases j <;> decide

private theorem stable_high (a : Word) (high : 0xfff700 ≤ a.toNat) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress a := by
  unfold GroupedBalancedSignBottomLeafTickData67.StableAddress
  have ne (w : Word) (hw : w.toNat < 0xfff700) : a ≠ w := by
    intro eq
    have h := congrArg BitVec.toNat eq
    omega
  refine ⟨Or.inr (by omega), ne _ (by decide), ne _ (by decide),
    ne _ (by decide), ne _ (by decide), ne _ (by decide),
    ne _ (by decide), ?_, ?_, ?_, ?_⟩
  all_goals
    intro i
    exact ne _ (by fin_cases i <;> decide)

theorem loaded_all_bottom_leaves_stack (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial finish : MachineState, ∃ n c : Nat,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial n c 2050 2052 finish ∧
      finish.pc = 0x14ec ∧
      (∀ j : Nat, j < 1024 →
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 0) =
          (GroupedBottomTree.leafRoot hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)) + j)).extractLsb' 0 64 ∧
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 1) =
          (GroupedBottomTree.leafRoot hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)) + j)).extractLsb' 64 64) ∧
      finish.getMem 0x81060 = 10 ∧
      finish.getMem 0x810d0 = 1024 ∧
      finish.getMem 0x810f8 = 0x20090 ∧
      (∀ i : Fin 3,
        finish.getMem (Signing.wordAddress 0x810a8 i.val) =
          (BitVec.ofNat 192 (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)))).extractLsb'
              (64*i.val) 64) ∧
      finish.getMem 0x810e8 =
        (finish.getMem 0x81090 &&& 1023#64) ∧
      (∀ i : Fin 3,
        finish.getMem (Signing.wordAddress 0x81090 i.val) =
          (BitVec.ofNat 192 (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat).extractLsb'
              (64*i.val) 64) ∧
      finish.getMem 0x81000 = 0 ∧
      finish.getReg .x2 = 0xfff700 ∧
      (∀ i : Fin 4, finish.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat →
        finish.getMem a = initial.getMem a) ∧
      n ≤ 170277 ∧ c ≤ 184643 ∧
      (∀ i : Fin 4,
        finish.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        finish.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) := by
  obtain ⟨initial,randomized,h5Ready,h5After,loaded,prefixRun,randomPc,
    h5ReadyPc,h5AfterPc,randomValue,h5Query,h5AfterEq,h5Words,keyWords,h5High,
    h5RandomWords⟩ :=
    GroupedBalancedSignIndexPrefix67.loaded_two_hash_prefix
      hash secretKey cache message
  let randomizer := Reference.randomizer hash secretKey message
  let answer := hash (SecurityRandomOracle.indexInput message randomizer)
  let index := answer.extractLsb' 0 160
  let leaf := leafIndex index
  have indexEq : index = Reference.indexOf hash message randomizer := by rfl
  obtain ⟨stored,extract,storedPc,storedLow,storedHigh,storedKey,storedHighFrame,
    extractRandomFrame⟩ :=
    GroupedBalancedSignIndexExtract67.extract_answer h5After answer
      h5AfterPc h5Words
  have low : (stored.getMem 0x81090 &&& 18446744073709550592#64) =
      (BitVec.ofNat 192 leaf).extractLsb' 0 64 := by
    rw [show stored.getMem 0x81090 = answer.extractLsb' 0 64 from by
      simpa [Signing.wordAddress] using storedLow 0]
    rw [answerLow answer]
    exact (leafLow index).symm
  have middle : stored.getMem 0x81098 =
      (BitVec.ofNat 192 leaf).extractLsb' 64 64 := by
    rw [show stored.getMem 0x81098 = answer.extractLsb' 64 64 from by
      simpa [Signing.wordAddress] using storedLow 1]
    rw [answerMid answer]
    exact (leafMid index).symm
  have high : stored.getMem 0x810a0 =
      (BitVec.ofNat 192 leaf).extractLsb' 128 64 := by
    rw [storedHigh,answerHigh answer]
    exact (leafHigh index).symm
  have storedSecret : ∀ i : Fin 4,
      stored.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [storedKey i]
    exact keyWords i
  obtain ⟨start,setupTrace,initialInv,startHeight,startCount,startWitness,
    startRounded,startSelected,startIndexWords,startHighFrame,
    setupRandomFrame⟩ :=
    GroupedBalancedSignBottomLoopStart67.setup_initial hash stored
      secretKey leaf storedPc low middle high storedSecret
  have indexAlign : leaf % 1024 = 0 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_align index
  have indexBound : leaf + 1024 ≤ 2^160 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_bound index
  obtain ⟨n,c,finish,bottomTrace,finishPc,stackWords,stable,bottomSp,
    nBound,cBound,seedWitness⟩ :=
    GroupedBalancedSignBottomLeafStack67.run_all_stack hash secretKey
      leaf (start.getMem 0x810e8) start indexBound indexAlign initialInv
  have lowWord : stored.getMem 0x81090 = index.extractLsb' 0 64 := by
    rw [show stored.getMem 0x81090 = answer.extractLsb' 0 64 from by
      simpa [Signing.wordAddress] using storedLow 0,
      answerLow answer]
  have selectedNat : (start.getMem 0x810e8).toNat =
      (index.extractLsb' 0 10).toNat := by
    rw [startSelected,lowWord]
    exact GroupedBalancedSignBottomIndexBounds67.low_word_eq_low index
  have selectedBound : (start.getMem 0x810e8).toNat < 1024 := by
    rw [selectedNat]
    exact (index.extractLsb' 0 10).isLt
  have selectedIndex : leaf + (start.getMem 0x810e8).toNat = index.toNat := by
    rw [selectedNat]
    exact GroupedBalancedSignBottomIndexBounds67.leafIndex_plus_low index
  refine ⟨initial,finish,196+25+72+n,226+25+72+c,loaded,?_,finishPc,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by omega,by omega,?_,?_⟩
  · have extractTrace := OrdinarySteps.trace (hash := hash) extract
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ((prefixRun.trans extractTrace).trans setupTrace).trans bottomTrace
  · intro j hj
    simpa only [leaf,indexEq,randomizer] using stackWords j hj
  · exact (stable 0x81060 (stable_control _ (Or.inl rfl))).trans startHeight
  · exact (stable 0x810d0 (stable_control _ (Or.inr (Or.inl rfl)))).trans startCount
  · exact (stable 0x810f8 (stable_control _ (Or.inr (Or.inr (Or.inl rfl))))).trans startWitness
  · intro i
    rw [stable _ (stable_rounded i)]
    simpa only [leaf,indexEq,randomizer] using startRounded i
  · rw [stable 0x810e8 (stable_control _
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      startSelected,stable 0x81090 (stable_control _
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]
    simpa [Signing.wordAddress] using
      congrArg (fun w : Word => w &&& 1023#64) (startIndexWords 0).symm
  · intro i
    rw [stable _ (stable_index i),startIndexWords i]
    fin_cases i
    · change stored.getMem 0x81090 =
        (BitVec.ofNat 192 index.toNat).extractLsb' 0 64
      rw [show stored.getMem 0x81090 = answer.extractLsb' 0 64 from by
        simpa [Signing.wordAddress] using storedLow 0,
        answerLow answer]
      exact (widenedSlice index 0).symm
    · change stored.getMem 0x81098 =
        (BitVec.ofNat 192 index.toNat).extractLsb' 64 64
      rw [show stored.getMem 0x81098 = answer.extractLsb' 64 64 from by
        simpa [Signing.wordAddress] using storedLow 1,
        answerMid answer]
      exact (widenedSlice index 64).symm
    · change stored.getMem 0x810a0 =
        (BitVec.ofNat 192 index.toNat).extractLsb' 128 64
      rw [storedHigh,answerHigh answer]
      have widen : index.zeroExtend 192 = BitVec.ofNat 192 index.toNat := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_setWidth]
      rw [widen]
  · have safe : GroupedBalancedSignBottomLeafTickData67.StableAddress
        0x81000 := by
      unfold GroupedBalancedSignBottomLeafTickData67.StableAddress
      simp [Signing.wordAddress]
      constructor <;> intro i <;> fin_cases i <;> decide
    exact (stable 0x81000 safe).trans initialInv.2.2.2.1
  · have initialPc := GroupedBalancedSignPrefixStack67.loaded_pc
      secretKey cache message initial loaded
    have prefixSp := GroupedBalancedSignPrefixStack67.prefix_sp
      hash initial h5After initialPc prefixRun
    have extractSp := GroupedBalancedSignIndexExtractStack67.extract_sp
      h5After stored h5AfterPc extract
    have setupSp := GroupedBalancedSignBottomSetupStack67.setup_sp
      hash stored start storedPc setupTrace
    exact bottomSp.trans (setupSp.trans (extractSp.trans
      (prefixSp.trans (GroupedBalancedSignPrefixStack67.loaded_stack
        secretKey cache message initial loaded))))
  · intro i
    exact (stable _ (stable_key i)).trans (initialInv.2.2.2.2.2.1 i)
  · intro a high
    exact (stable a (stable_high a high)).trans
      ((startHighFrame a high).trans
        ((storedHighFrame a high).trans (h5High a high)))
  · intro i
    rw [stable _ (stable_randomizer i),
      setupRandomFrame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide),
      extractRandomFrame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]
    exact h5RandomWords i
  · intro i
    have hs := seedWitness i selectedBound
    rw [selectedIndex] at hs
    exact hs

#print axioms loaded_all_bottom_leaves_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedStack67
