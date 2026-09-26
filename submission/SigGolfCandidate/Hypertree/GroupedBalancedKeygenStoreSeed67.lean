import SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashMemory67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretCopy67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashEntry67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenStoreSeed67. -/
section
/-! The loaded keygen state reaches its first private-seed hash with initialized controls. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretCopy67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem branch_x19_zero (s : MachineState)
    (zero : s.getMem 0x81030 = 0) :
    (GroupedBalancedKeygenBranch67.branchState s).getReg .x19 = 0 := by
  simp [GroupedBalancedKeygenBranch67.branchState, execInstrBr,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  exact zero

private theorem prepare_tree_zero (s : MachineState)
    (zero : s.getReg .x19 = 0) :
    (prepareState s).getMem 0x81030 = 0 := by
  simp [prepareState, execInstrBr, signExtend12, zero,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

private theorem control_disjoint (a : Word) (ha : 0x81000 ≤ a.toNat) :
    ∀ i, i < 4 → a ≠ Signing.wordAddress 0x80020 i := by
  intro i hi same
  have hn := congrArg BitVec.toNat same
  simp only [Signing.wordAddress, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80020+8*i < 2^64)] at hn
  omega

theorem initial_secret_copy_controls (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    ∃ final, Trace hash GroupedBalancedKeygenImage67.image s
        57 57 0 0 final ∧
      final.pc = 0x10a0 ∧
      final.getMem 0x81000 = 156 ∧
      final.getMem 0x81008 = 0 ∧
      final.getMem 0x81010 = 0 ∧
      final.getMem 0x81018 = 0 ∧
      final.getMem 0x81030 = 0 ∧
      final.getReg .x19 = 0 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) := by
  let entered := GroupedBalancedKeygenPrefix67.entryState s
  let branched := GroupedBalancedKeygenBranch67.branchState entered
  obtain ⟨first,firstPC⟩ :=
    GroupedBalancedKeygenBranch67.initial_branch_trace hash s pc
  obtain ⟨final,second,secondPC,words,frame,x19⟩ :=
    secret_copy_frame branched firstPC
  have ewords := GroupedBalancedKeygenPrefix67.entry_words s
  have bmem (a : Word) : branched.getMem a = entered.getMem a :=
    GroupedBalancedKeygenBranch67.branch_mem entered a
  have control (a : Word) (ha : 0x81000 ≤ a.toNat)
      (hne : a ≠ 0x81030) : final.getMem a = entered.getMem a := by
    rw [frame a (control_disjoint a ha)]
    rw [prepare_mem_other branched a hne, bmem]
  refine ⟨final,?_,secondPC,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [GroupedBalancedKeygenBranch67.image,
      GroupedBalancedKeygenSecretCopy67.image, Nat.reduceAdd] using
        first.trans second.trace
  · rw [control 0x81000 (by decide) (by decide)]
    exact ewords.1
  · rw [control 0x81008 (by decide) (by decide)]
    exact ewords.2.1
  · rw [control 0x81010 (by decide) (by decide)]
    exact ewords.2.2.1
  · rw [control 0x81018 (by decide) (by decide)]
    exact ewords.2.2.2.1
  · rw [frame 0x81030 (control_disjoint 0x81030 (by decide))]
    apply prepare_tree_zero
    apply branch_x19_zero
    exact ewords.2.2.2.2
  · rw [x19]
    apply branch_x19_zero
    exact ewords.2.2.2.2
  · intro i hi
    rw [words i hi, GroupedBalancedKeygenBranch67.branch_mem,
      GroupedBalancedKeygenSecretCopy67.entry_source_word s i hi]

#print axioms initial_secret_copy_controls

theorem first_hash_ready (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) (secretKey : SecretKey)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ prepared, Trace hash GroupedBalancedKeygenImage67.image s
        95 95 0 0 prepared ∧
      prepared.pc = 0x1138 ∧
      hashInput prepared = Reference.packed
        (KeygenDomain.secretPayload
          (KeygenDomain.header 1 156 0 0 0) 0 secretKey) ∧
      prepared.getReg .x5 = 1 ∧
      prepared.getReg .x10 = 0x80000 ∧
      prepared.getReg .x11 = 512 ∧
      prepared.getReg .x12 = 0x80300 ∧
      prepared.getReg .x19 = 0 := by
  obtain ⟨copied,first,copiedPC,level,index0,index1,index2,tree,copiedX19,content⟩ :=
    initial_secret_copy_controls hash s pc
  have copiedSecret : ∀ i : Fin 4,
      copied.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [content i i.isLt,secret i]
  let prepared := GroupedBalancedKeygenFirstHash67.preHashState copied
  have second := (GroupedBalancedKeygenFirstHash67.pre_hash_steps
    copied copiedPC level tree).trace (hash := hash)
  refine ⟨prepared,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [GroupedBalancedKeygenFirstHash67.image,Nat.reduceAdd] using
      first.trans second
  · exact GroupedBalancedKeygenFirstHashFields67.pre_hash_pc copied copiedPC
  · exact GroupedBalancedKeygenFirstHashMemory67.first_hash_input
      copied secretKey level tree index0 index1 index2 copiedSecret
  · exact (GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied).1
  · exact (GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied).2.1
  · exact (GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied).2.2.1
  · exact (GroupedBalancedKeygenFirstHashFields67.pre_hash_regs copied).2.2.2
  · rw [GroupedBalancedKeygenFirstHashFields67.pre_hash_x19]
    exact copiedX19

#print axioms first_hash_ready

theorem first_hash_call (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) (secretKey : SecretKey)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ after, Trace hash GroupedBalancedKeygenImage67.image s
        96 103 1 1 after ∧
      after.pc = 0x113c ∧
      (∀ i : Fin 2,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (Reference.truncate
            (Reference.query hash 1 156 0 0 0 0 (bytes secretKey))).extractLsb'
              (64*i.val) 64) ∧
      (∀ i : Fin 4,
        after.getMem (Signing.wordAddress 0x80300 i.val) =
          (Reference.query hash 1 156 0 0 0 0 (bytes secretKey)).extractLsb'
            (64*i.val) 64) ∧
      after.getReg .x19 = 0 := by
  obtain ⟨prepared,first,readyPC,input,service,source,bits,destination,x19⟩ :=
    first_hash_ready hash s pc secretKey secret
  have code : fetch GroupedBalancedKeygenImage67.image prepared =
      some (.base .ECALL) := by
    have hc : Keygen.instructionAt GroupedBalancedKeygenImage67.image 0x1138 =
        some (.base .ECALL) := by decide
    simpa only [Keygen.fetch_at,readyPC] using hc
  let after := writeHash prepared (hash (hashInput prepared))
  have second := KeygenDomain.secret_hash_trace
    GroupedBalancedKeygenImage67.image hash prepared
    code service source bits destination
  have q : hash (hashInput prepared) =
      Reference.query hash 1 156 0 0 0 0 (bytes secretKey) := by
    rw [input]
    rfl
  refine ⟨after,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · simp [after,Keygen.hash_pc,readyPC]
  · intro i
    rw [Signing.hash_answer_word prepared (hash (hashInput prepared))
      destination ⟨i.val,by have := i.isLt; omega⟩]
    rw [q]
    let result := Reference.query hash 1 156 0 0 0 0 (bytes secretKey)
    change result.extractLsb' (64*i.val) 64 =
      (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
    fin_cases i <;> ext j hj <;> simp (disch := omega)
  · intro i
    rw [Signing.hash_answer_word prepared (hash (hashInput prepared))
      destination i, q]
  · rw [Keygen.hash_registers]
    exact x19

#print axioms first_hash_call

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFirstHashEntry67

end

/-! The keygen copies its first 32-byte H1 answer into the top-tree seed cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenStoreSeed67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.SD .x28 .x19 0)
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0xd00)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x113c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1140 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1144 = some (.base (.SD .x28 .x19 0)) ∧
    Keygen.instructionAt image 0x1148 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x114c = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x1150 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1154 = some (.base (.ADDI .x7 .x7 0xd00)) ∧
    Keygen.instructionAt image 0x1158 = some (.base (.ADDI .x10 .x0 4)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x113c) :
    OrdinarySteps image s 8 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 48)
  let s3 := execInstrBr s2 (.SD .x28 .x19 0)
  let s4 := execInstrBr s3 (.LUI .x6 0x80)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 0x300)
  let s6 := execInstrBr s5 (.LUI .x7 0x81)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 0xd00)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 48)) 6
  · have hp : s1.pc = 0x1140 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x19 0)) 5
  · have hp : s2.pc = 0x1144 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x6 0x80)) 4
  · have hp : s3.pc = 0x1148 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s4.pc = 0x114c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s5.pc = 0x1150 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 0xd00)) 1
  · have hp : s6.pc = 0x1154 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s7.pc = 0x1158 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x113c) :
    (setupState s).pc = 0x115c ∧
    (setupState s).getReg .x6 = 0x80300 ∧
    (setupState s).getReg .x7 = 0x80d00 ∧
    (setupState s).getReg .x10 = 4 := by
  simp [setupState,execInstrBr,signExtend12,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem_other (s : MachineState) (a : Word)
    (hne : a ≠ 0x81030) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro same
  exact False.elim (hne same)

theorem setup_counter (s : MachineState) :
    (setupState s).getMem 0x81030 = s.getReg .x19 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_code : Keygen.CopyCode image 0x115c := by
  unfold Keygen.CopyCode image GroupedBalancedKeygenImage67.image
  decide

theorem copy_seed (s : MachineState) (pc : s.pc = 0x113c) :
    ∃ final, OrdinarySteps image s 32 final ∧
      final.pc = 0x1174 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80d00 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      (∀ a, (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80d00 i) →
        final.getMem a = (setupState s).getMem a) ∧
      final.getReg .x19 = s.getReg .x19 := by
  let ready := setupState s
  obtain ⟨readyPC,readySrc,readyDst,readyCount⟩ := setup_fields s pc
  have readyInv : Keygen.CopyInvariant 0x115c 0x80300 0x80d00 4 4 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨final,copied,done,words,frame,x19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x115c copy_code
      0x80300 0x80d00 4 ready readyInv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,?_,?_,frame,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready final 8 (6*4)
        (setup_steps s pc) copied
  · simpa [Keygen.CopyInvariant] using done.2.2.1
  · intro i hi
    rw [words i hi,setup_mem_other s (Signing.wordAddress 0x80300 i) ?_]
    intro same
    have hn := congrArg BitVec.toNat same
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80300+8*i < 2^64)] at hn
    have hc : (0x81030 : Word).toNat = 0x81030 := by decide
    rw [hc] at hn
    omega
  · rw [x19]
    change (setupState s).getReg .x19 = s.getReg .x19
    simp [setupState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms copy_seed

theorem initial_seed_cache (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) (secretKey : SecretKey)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ cached, Trace hash image s 128 135 1 1 cached ∧
      cached.pc = 0x1174 ∧
      cached.getReg .x19 = 0 ∧
      (∀ i : Fin 4,
        cached.getMem (Signing.wordAddress 0x80d00 i.val) =
          (Reference.query hash 1 156 0 0 0 0 (bytes secretKey)).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨hashed,first,hashedPC,_,answer,hashedX19⟩ :=
    GroupedBalancedKeygenFirstHashEntry67.first_hash_call
      hash s pc secretKey secret
  obtain ⟨cached,second,cachedPC,words,_,cachedX19⟩ := copy_seed hashed hashedPC
  refine ⟨cached,?_,cachedPC,?_,?_⟩
  · simpa only [image,Nat.reduceAdd] using first.trans second.trace
  · rw [cachedX19]
    exact hashedX19
  · intro i
    rw [words i i.isLt, answer i]

#print axioms initial_seed_cache

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenStoreSeed67
