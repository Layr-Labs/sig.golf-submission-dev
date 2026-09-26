import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashMemory67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenSeedRun67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.TraceDeterminism

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretQuery67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSeed67. -/
section
/-! General private-pair input semantics for the direct67 keygen image. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenFirstHash67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem header_eq (base pair : Nat) :
    (1 : Word) + (BitVec.ofNat 64 base <<< 8) +
      (BitVec.ofNat 64 pair <<< 24) =
        KeygenDomain.header 1 base 0 pair 0 := by
  simp [KeygenDomain.header, KeygenDomain.shift_ofNat,
    BitVec.ofNat_add, BitVec.ofNat_mul, Nat.add_assoc, BitVec.add_assoc]

theorem private_input (s : MachineState) (secretKey : SecretKey)
    (base tree pair : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 pair)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    hashInput (preHashState s) = Reference.packed
      (KeygenDomain.secretPayload
        (KeygenDomain.header 1 base 0 pair 0) tree secretKey) := by
  have words : ∀ i : Fin 8,
      (preHashState s).getMem (Signing.wordAddress 0x80000 i.val) =
        KeygenDomain.secretInputWord
          (KeygenDomain.header 1 base 0 pair 0) tree secretKey i := by
    apply KeygenDomain.secret_words_of_layout
    · simp only [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem,
        if_true]
      rw [level, counter]
      exact header_eq base pair
    · intro i
      have h := address i
      fin_cases i <;> simpa [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem,
        Signing.wordAddress] using h
    · intro i
      rw [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
      have h := secret i
      fin_cases i <;> simpa [Signing.wordAddress] using h
  obtain ⟨_, source, bits, _⟩ :=
    GroupedBalancedKeygenFirstHashFields67.pre_hash_regs s
  exact KeygenDomain.secret_query_eq (preHashState s)
    (KeygenDomain.header 1 base 0 pair 0) tree secretKey source bits words

theorem private_answer (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (base tree pair : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 pair)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    hash (hashInput (preHashState s)) =
      Reference.query hash 1 base tree 0 pair 0 (bytes secretKey) := by
  rw [private_input s secretKey base tree pair level counter address secret]
  rfl

#print axioms private_input
#print axioms private_answer
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretQuery67

end

/-! The direct67 keygen H1 answer supplies both seeds of each WOTS pair. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev branch := GroupedBalancedKeygenBranch67.branchState
private abbrev prepare := GroupedBalancedKeygenSecretCopy67.prepareState

private theorem pair_shift (k : Nat) (bound : k ≤ 33) :
    ((BitVec.ofNat 64 (2*k) : Word) >>> 1) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2*k < 2^64),
    Nat.mod_eq_of_lt (by omega : k < 2^64), Nat.shiftRight_eq_div_pow]
  omega

theorem prepared_pair (s : MachineState) (k : Nat) (bound : k ≤ 33)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k)) :
    (prepare (branch s)).getMem 0x81030 = BitVec.ofNat 64 k := by
  simp [prepare,GroupedBalancedKeygenSecretCopy67.prepareState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    GroupedBalancedKeygenOddSeed67.branch_x19]
  exact (congrArg (fun w : Word => w >>> 1) counter).trans
    (pair_shift k bound)

theorem even_seed_copy_other (s final : MachineState)
    (pc : s.pc = 0x1174) (even : s.getReg .x19 &&& 1 = 0)
    (trace : OrdinarySteps image s 19 final) (a : Word)
    (outside : ∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) :
    final.getMem a = s.getMem a := by
  let selected := GroupedBalancedKeygenFirstLeaf67.branchState s
  have first := GroupedBalancedKeygenFirstLeaf67.branch_steps s pc
  have selectedPC := GroupedBalancedKeygenEvenSeedAny67.branch_even_pc s pc even
  let ready := GroupedBalancedKeygenFirstLeaf67.setupState selected
  have second := GroupedBalancedKeygenFirstLeaf67.setup_steps selected selectedPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,readyX19⟩ :=
    GroupedBalancedKeygenFirstLeaf67.setup_fields selected selectedPC
  have inv : Keygen.CopyInvariant 0x11c0 0x80d00 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨made,third,_,_,frame,_⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x11c0
      GroupedBalancedKeygenFirstLeaf67.copy_code
      0x80d00 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have path : OrdinarySteps image s 19 made := by
    have prepath := Keygen.ordinary_trans image s selected ready 2 5 first second
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready made 7 (6*2) prepath third
  have same : final = made := Trace.deterministic
    (trace.trace (hash := fun _ => 0)) (path.trace (hash := fun _ => 0))
  subst final
  rw [frame a outside,
    GroupedBalancedKeygenFirstLeaf67.setup_mem,
    GroupedBalancedKeygenFirstLeaf67.branch_mem]

theorem even_seed_copy_cache (s final : MachineState)
    (pc : s.pc = 0x1174) (even : s.getReg .x19 &&& 1 = 0)
    (trace : OrdinarySteps image s 19 final) :
    ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80d10 i.val) =
        s.getMem (Signing.wordAddress 0x80d10 i.val) := by
  intro i
  exact even_seed_copy_other s final pc even trace _
    (by intro j hj; fin_cases i <;> interval_cases j <;> decide)

theorem even_seed_h1 (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf k : Nat) (bound : k ≤ 33)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 127 134 1 1 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = BitVec.ofNat 64 (2*k) ∧
      final.getMem 0x81030 = BitVec.ofNat 64 (2*k) ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = s.getMem 0x81008 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80d10 i.val) =
          (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
            (128+64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x81010 i.val) =
          s.getMem (Signing.wordAddress 0x81010 i.val)) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a = s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [counter]
    have h := bound
    interval_cases k <;> decide
  have selectedPC := GroupedBalancedKeygenEvenSeedRun67.branch_even_pc s pc even
  let staged := prepare selected
  obtain ⟨copied,second,copiedPC,copiedSecret,copyFrame,copiedX19⟩ :=
    GroupedBalancedKeygenSecretCopy67.secret_copy_frame selected selectedPC
  have copiedFrame (a : Word) (high : 0x81000 ≤ a.toNat)
      (notPair : a ≠ 0x81030) : copied.getMem a = s.getMem a := by
    rw [copyFrame a (by
      intro i hi same
      have hn := congrArg BitVec.toNat same
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i < 2^64)] at hn
      omega),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected a notPair,
      GroupedBalancedKeygenBranch67.branch_mem]
  have copiedLevel : copied.getMem 0x81000 = 156 := by
    rw [copiedFrame 0x81000 (by decide) (by decide)]
    exact level
  have copiedAddress : ∀ i : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    rw [copiedFrame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact address i
  have copiedPair : copied.getMem 0x81030 = BitVec.ofNat 64 k := by
    rw [copyFrame 0x81030 (by
      intro i hi
      interval_cases i <;> decide)]
    exact prepared_pair s k bound counter
  have copiedKey : ∀ i : Fin 4,
      copied.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [copiedSecret i.val i.isLt,GroupedBalancedKeygenBranch67.branch_mem]
    exact secret i
  let ready := GroupedBalancedKeygenFirstHash67.preHashState copied
  have third : OrdinarySteps image copied 38 ready := by
    simpa only [image,GroupedBalancedKeygenFirstHash67.image,ready] using
      GroupedBalancedKeygenFirstHash67.pre_hash_steps_any
        copied copiedPC copiedLevel
  have readyPC := GroupedBalancedKeygenFirstHashFields67.pre_hash_pc copied copiedPC
  obtain ⟨service,source,bits,destination⟩ :=
    GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied
  have code : fetch image ready = some (.base .ECALL) := by
    have hc : Keygen.instructionAt image 0x1138 = some (.base .ECALL) := by
      unfold image GroupedBalancedKeygenImage67.image
      decide
    change Keygen.instructionAt image ready.pc = some (.base .ECALL)
    rw [readyPC]
    exact hc
  let hashed := writeHash ready (hash (hashInput ready))
  have fourth : Trace hash image ready 1 8 1 1 hashed :=
    KeygenDomain.secret_hash_trace image hash ready code
      service source bits destination
  have hashedPC : hashed.pc = 0x113c := by
    change ready.pc + 4 = 0x113c
    rw [show ready.pc = 0x1138 from readyPC]
    decide
  have answer : hash (hashInput ready) =
      GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k := by
    exact GroupedBalancedKeygenSecretQuery67.private_answer hash copied
      secretKey 156 leaf k copiedLevel copiedPair copiedAddress copiedKey
  have hashedWords : ∀ i : Fin 4,
      hashed.getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
          (64*i.val) 64 := by
    intro i
    rw [Signing.hash_answer_word ready (hash (hashInput ready)) destination i,
      answer]
  obtain ⟨cached,fifth,cachedPC,cachedWords,cacheFrame,cachedX19⟩ :=
    GroupedBalancedKeygenStoreSeed67.copy_seed hashed hashedPC
  have cachedSeed : ∀ i : Fin 4,
      cached.getMem (Signing.wordAddress 0x80d00 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
          (64*i.val) 64 := by
    intro i
    rw [cachedWords i.val i.isLt,hashedWords i]
  have cachedIndex : cached.getReg .x19 = BitVec.ofNat 64 (2*k) := by
    rw [cachedX19,Keygen.hash_registers,
      GroupedBalancedKeygenFirstHashFields67.pre_hash_x19,copiedX19,
      GroupedBalancedKeygenOddSeed67.branch_x19,counter]
  have cachedEven : cached.getReg .x19 &&& 1 = 0 := by
    rw [cachedIndex,← counter]
    exact even
  obtain ⟨final,sixth,finalPC,finalIndex,finalCounter,finalLevel,finalLeaf,finalWords⟩ :=
    GroupedBalancedKeygenEvenSeedAny67.even_seed_copy cached cachedPC cachedEven
  have path0 : Trace hash image s 37 37 0 0 copied := by
    simpa only [image,GroupedBalancedKeygenBranch67.image,
      GroupedBalancedKeygenSecretCopy67.image,Nat.reduceAdd] using
      (first.trace (hash := hash)).trans (second.trace (hash := hash))
  have path1 : Trace hash image s 75 75 0 0 ready := by
    simpa only [Nat.reduceAdd] using path0.trans (third.trace (hash := hash))
  have path2 : Trace hash image s 76 83 1 1 hashed := by
    simpa only [Nat.reduceAdd] using path1.trans fourth
  have path3 : Trace hash image s 108 115 1 1 cached := by
    simpa only [image,GroupedBalancedKeygenStoreSeed67.image,
      Nat.reduceAdd] using path2.trans (fifth.trace (hash := hash))
  have total : Trace hash image s 127 134 1 1 final := by
    simpa only [Nat.reduceAdd] using path3.trans (sixth.trace (hash := hash))
  have cachedLevel : cached.getMem 0x81000 = 156 := by
    rw [cacheFrame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed 0x81000 (by decide),
      Signing.hash_answer_frame ready _ destination 0x81000
        (by intro i; fin_cases i <;> decide),
      GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
    exact copiedLevel
  have cachedLeaf : cached.getMem 0x81008 = s.getMem 0x81008 := by
    rw [cacheFrame 0x81008 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed 0x81008 (by decide),
      Signing.hash_answer_frame ready _ destination 0x81008
        (by intro i; fin_cases i <;> decide),
      GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
    exact copiedFrame 0x81008 (by decide) (by decide)
  have cachedCounter : cached.getMem 0x81030 = BitVec.ofNat 64 (2*k) := by
    rw [cacheFrame 0x81030 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_counter,
      Keygen.hash_registers,
      GroupedBalancedKeygenFirstHashFields67.pre_hash_x19,copiedX19,
      GroupedBalancedKeygenOddSeed67.branch_x19]
    exact counter
  have cachedControl (i : Fin 2) :
      cached.getMem (Signing.wordAddress 0x81010 i.val) =
        s.getMem (Signing.wordAddress 0x81010 i.val) := by
    have readyControl : ready.getMem (Signing.wordAddress 0x81010 i.val) =
        copied.getMem (Signing.wordAddress 0x81010 i.val) := by
      fin_cases i <;>
        simp [ready,GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem,
          Signing.wordAddress]
    rw [cacheFrame _ (by intro j hj; fin_cases i <;> interval_cases j <;> decide),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed _
        (by fin_cases i <;> decide),
      Signing.hash_answer_frame ready _ destination _
        (by intro j; fin_cases i <;> fin_cases j <;> decide),
      readyControl]
    exact copiedFrame _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
  refine ⟨final,total,finalPC,finalIndex.trans cachedIndex,
    finalCounter.trans cachedCounter,finalLevel.trans cachedLevel,
    finalLeaf.trans cachedLeaf,?_,?_,?_,?_,?_⟩
  · intro i
    rw [finalWords i.val i.isLt,cachedSeed ⟨i.val,by omega⟩]
  · intro i
    rw [even_seed_copy_cache cached final cachedPC cachedEven sixth i]
    have addressEq : Signing.wordAddress 0x80d10 i.val =
        Signing.wordAddress 0x80d00 (i.val+2) := by
      fin_cases i <;> decide
    rw [addressEq,cachedSeed ⟨i.val+2,by omega⟩]
    have idx : 64 * (i.val + 2) = 128 + 64 * i.val := by omega
    rw [idx]
  · intro i
    rw [even_seed_copy_other cached final cachedPC cachedEven sixth _
      (by intro j hj; fin_cases i <;> interval_cases j <;> decide)]
    exact cachedControl i
  · intro a lower upper
    have below (n : Nat) (small : n < 0x80800) :
        a ≠ BitVec.ofNat 64 n := by
      intro same
      rw [same] at lower
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : n < 2^64)] at lower
      omega
    have above (n : Nat) (large : 0x80d00 ≤ n) (small : n < 2^64) :
        a ≠ BitVec.ofNat 64 n := by
      intro same
      rw [same] at upper
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at upper
      omega
    rw [even_seed_copy_other cached final cachedPC cachedEven sixth a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        below (0x80020+8*j) (by omega))]
    rw [cacheFrame a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        above (0x80d00+8*j) (by omega) (by omega)),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed a
        (above 0x81030 (by omega) (by omega)),
      Signing.hash_answer_frame ready _ destination a (by
        intro j
        simpa only [Signing.wordAddress] using
          below (0x80300+8*j.val) (by have := j.isLt; omega))]
    rw [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
    rw [copyFrame a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        below (0x80020+8*j) (by omega)),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected a
        (above 0x81030 (by omega) (by omega)),
      GroupedBalancedKeygenBranch67.branch_mem]
    split_ifs with h0 h1 h2 h3
    · exact False.elim ((below 0x80018 (by omega)) h0)
    · exact False.elim ((below 0x80010 (by omega)) h1)
    · exact False.elim ((below 0x80008 (by omega)) h2)
    · exact False.elim ((below 0x80000 (by omega)) h3)
    · rfl
  · intro a small
    have ne (n : Nat) (large : 0x100 ≤ n) (bound : n < 2^64) :
        a ≠ BitVec.ofNat 64 n := by
      intro same
      rw [same] at small
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at small
      omega
    rw [even_seed_copy_other cached final cachedPC cachedEven sixth a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        ne (0x80020+8*j) (by omega) (by omega))]
    rw [cacheFrame a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        ne (0x80d00+8*j) (by omega) (by omega)),
      GroupedBalancedKeygenStoreSeed67.setup_mem_other hashed a
        (ne 0x81030 (by omega) (by omega)),
      Signing.hash_answer_frame ready _ destination a (by
        intro j
        simpa only [Signing.wordAddress] using
          ne (0x80300+8*j.val) (by omega) (by have := j.isLt; omega))]
    rw [GroupedBalancedKeygenFirstHashMemory67.pre_hash_mem]
    rw [copyFrame a (by
      intro j hj
      simpa only [Signing.wordAddress] using
        ne (0x80020+8*j) (by omega) (by omega)),
      GroupedBalancedKeygenSecretCopy67.prepare_mem_other selected a
        (ne 0x81030 (by omega) (by omega)),
      GroupedBalancedKeygenBranch67.branch_mem]
    split_ifs with h0 h1 h2 h3
    · exact False.elim ((ne 0x80018 (by omega) (by omega)) h0)
    · exact False.elim ((ne 0x80010 (by omega) (by omega)) h1)
    · exact False.elim ((ne 0x80008 (by omega) (by omega)) h2)
    · exact False.elim ((ne 0x80000 (by omega) (by omega)) h3)
    · rfl

theorem odd_seed_h1 (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf n : Nat)
    (pc : s.pc = 0x1050) (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
          (128+64*i.val) 64) :
    ∃ final,
      Trace hash image s 26 26 0 0 final ∧
      final.pc = 0x11d8 ∧
      final.getReg .x19 = BitVec.ofNat 64 n ∧
      final.getMem 0x81030 = BitVec.ofNat 64 n ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
            (128+64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80d10 i.val) =
          s.getMem (Signing.wordAddress 0x80d10 i.val)) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x81010 i.val) =
          s.getMem (Signing.wordAddress 0x81010 i.val)) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a = s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) := by
  let selected := branch s
  have first := GroupedBalancedKeygenBranch67.branch_steps s pc
  have selectedPC := GroupedBalancedKeygenOddSeed67.branch_odd_pc s pc odd
  let jumped := GroupedBalancedKeygenOddSeed67.jumpState selected
  have second := GroupedBalancedKeygenOddSeed67.jump_steps selected selectedPC
  have jumpedPC := GroupedBalancedKeygenOddSeed67.jump_pc selected selectedPC
  have jumpedOdd : jumped.getReg .x19 &&& 1 ≠ 0 := by
    rw [GroupedBalancedKeygenOddSeed67.jump_x19,
      GroupedBalancedKeygenOddSeed67.branch_x19]
    exact odd
  let leafBranch := GroupedBalancedKeygenFirstLeaf67.branchState jumped
  have third := GroupedBalancedKeygenFirstLeaf67.branch_steps jumped jumpedPC
  have leafPC := GroupedBalancedKeygenOddSeed67.leaf_odd_pc jumped jumpedPC jumpedOdd
  let ready := GroupedBalancedKeygenOddSeed67.setupState leafBranch
  have fourth := GroupedBalancedKeygenOddSeed67.setup_steps leafBranch leafPC
  obtain ⟨readyPC,readySrc,readyDst,readyCount,readyX19⟩ :=
    GroupedBalancedKeygenOddSeed67.setup_fields leafBranch leafPC
  have inv : Keygen.CopyInvariant 0x1190 0x80d10 0x80020 2 2 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨copied,fifth,done,words,frame,copyX19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x1190
      GroupedBalancedKeygenOddSeed67.copy_code
      0x80d10 0x80020 2 ready inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have copiedPC : copied.pc = 0x11a8 := by
    simpa [Keygen.CopyInvariant] using done.2.2.1
  let final := GroupedBalancedKeygenOddSeed67.finishState copied
  have sixth := GroupedBalancedKeygenOddSeed67.finish_steps copied copiedPC
  have finalPC := GroupedBalancedKeygenOddSeed67.finish_pc copied copiedPC
  have finalX19 : final.getReg .x19 = BitVec.ofNat 64 n := by
    rw [GroupedBalancedKeygenOddSeed67.finish_x19,copyX19,readyX19,
      GroupedBalancedKeygenOddSeed67.leaf_x19,
      GroupedBalancedKeygenOddSeed67.jump_x19,
      GroupedBalancedKeygenOddSeed67.branch_x19,counter]
  have finalCounter : final.getMem 0x81030 = BitVec.ofNat 64 n := by
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame 0x81030 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
    exact counter
  have finalLevel : final.getMem 0x81000 = s.getMem 0x81000 := by
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame 0x81000 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame 0x81008 (by intro i hi; interval_cases i <;> decide),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have finalSeed : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
          (128+64*i.val) 64 := by
    intro i
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,words i.val i.isLt,
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
    exact cached i
  have finalCached : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80d10 i.val) =
        s.getMem (Signing.wordAddress 0x80d10 i.val) := by
    intro i
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame _ (by
        intro j hj
        fin_cases i <;> interval_cases j <;> decide),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have finalControl : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x81010 i.val) =
        s.getMem (Signing.wordAddress 0x81010 i.val) := by
    intro i
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame _ (by intro j hj; fin_cases i <;> interval_cases j <;> decide),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have finalTable : ∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
      final.getMem a = s.getMem a := by
    intro a lower upper
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame a (by
        intro j hj same
        have hn := congrArg BitVec.toNat same
        simp only [Signing.wordAddress,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 0x80020+8*j < 2^64)] at hn
        omega),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have finalSource : ∀ a : Word, a.toNat < 0x100 →
      final.getMem a = s.getMem a := by
    intro a small
    rw [GroupedBalancedKeygenOddSeed67.finish_mem,
      frame a (by
        intro j hj same
        have hn := congrArg BitVec.toNat same
        simp only [Signing.wordAddress,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 0x80020+8*j < 2^64)] at hn
        omega),
      GroupedBalancedKeygenOddSeed67.setup_mem,
      GroupedBalancedKeygenFirstLeaf67.branch_mem,
      GroupedBalancedKeygenOddSeed67.jump_mem,
      GroupedBalancedKeygenBranch67.branch_mem]
  have path0 : OrdinarySteps image s 6 jumped :=
    Keygen.ordinary_trans image s selected jumped 5 1 first second
  have path1 : OrdinarySteps image s 8 leafBranch :=
    Keygen.ordinary_trans image s jumped leafBranch 6 2 path0 third
  have path2 : OrdinarySteps image s 13 ready :=
    Keygen.ordinary_trans image s leafBranch ready 8 5 path1 fourth
  have path3 : OrdinarySteps image s 25 copied :=
    Keygen.ordinary_trans image s ready copied 13 12 path2 fifth
  have path4 : OrdinarySteps image s 26 final :=
    Keygen.ordinary_trans image s copied final 25 1 path3 sixth
  exact ⟨final,path4.trace (hash := hash),finalPC,finalX19,
    finalCounter,finalLevel,finalLeaf,finalSeed,finalCached,finalControl,
    finalTable,finalSource⟩

theorem even_secret_words (hash : Hash) (secretKey : SecretKey)
    (leaf k : Nat) (bound : k ≤ 33) (i : Fin 2) :
    (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
      (64*i.val) 64 =
    (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
      ⟨2*k,by omega⟩).extractLsb' (64*i.val) 64 := by
  have quotient : 2*k/2 = k := by omega
  have parity : 2*k%2 = 0 := by omega
  simp only [GroupedBalancedUpperTree67.secret,Fin.val_mk,quotient,parity,
    if_pos rfl]
  fin_cases i
  · ext j hj
    simp (disch := omega)
  · ext j hj
    simp (disch := omega)

theorem odd_secret_words (hash : Hash) (secretKey : SecretKey)
    (leaf n : Nat) (bound : n < 67) (parity : n%2 = 1) (i : Fin 2) :
    (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
      (128+64*i.val) 64 =
    (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
      ⟨n,bound⟩).extractLsb' (64*i.val) 64 := by
  simp only [GroupedBalancedUpperTree67.secret,parity,
    show (1:Nat)=0 ↔ False from by decide,if_false]
  fin_cases i
  · ext j hj
    simp (disch := omega)
  · ext j hj
    simp (disch := omega)
    congr 1
    omega

#print axioms prepared_pair
#print axioms even_seed_h1
#print axioms odd_seed_h1
#print axioms even_secret_words
#print axioms odd_secret_words

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSeed67
