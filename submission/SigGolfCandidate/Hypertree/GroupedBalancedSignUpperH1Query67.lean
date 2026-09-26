import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Index67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.KeygenDomain

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Ready67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Query67. -/
section
/-! Configure the paired H1 query's source, bit count, output, and service. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Ready67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def readyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 512)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

private theorem ready_code :
    Keygen.instructionAt image 0x1830 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 0x1834 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1838 = some (.base (.ADDI .x11 .x0 512)) ∧
    Keygen.instructionAt image 0x183c = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 0x1840 = some (.base (.ADDI .x12 .x12 0x300)) ∧
    Keygen.instructionAt image 0x1844 = some (.base (.ADDI .x5 .x0 1)) := by decide

theorem ready_steps (s : MachineState) (pc : s.pc = 0x1830) :
    OrdinarySteps image s 6 (readyState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 512)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x300)
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := ready_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 512)) 3
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 (readyState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem ready_pc (s : MachineState) (pc : s.pc = 0x1830) :
    (readyState s).pc = 0x1848 := by
  simp [readyState,execInstrBr,pc]

theorem ready_regs (s : MachineState) :
    (readyState s).getReg .x10 = 0x80000 ∧
    (readyState s).getReg .x11 = 512 ∧
    (readyState s).getReg .x12 = 0x80300 ∧
    (readyState s).getReg .x5 = 1 := by
  simp [readyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem ready_frame (s : MachineState) (a : Word) :
    (readyState s).getMem a = s.getMem a := by
  simp [readyState,execInstrBr]

#print axioms ready_steps
#print axioms ready_pc
#print axioms ready_regs
#print axioms ready_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Ready67

end

/-! The upper signer's paired H1 machine query agrees with the functional
secret-pair derivation. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def prepared (s : MachineState) : MachineState :=
  GroupedBalancedSignUpperH1Ready67.readyState
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))

theorem prepared_steps (s : MachineState) (pc : s.pc = 0x17b0) :
    OrdinarySteps image s 38 (prepared s) := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  have htrace := GroupedBalancedSignUpperH1Header67.header_steps s pc
  have itrace := GroupedBalancedSignUpperH1Index67.index_steps h
    (GroupedBalancedSignUpperH1Header67.header_pc s pc)
  have rtrace := GroupedBalancedSignUpperH1Ready67.ready_steps i
    (GroupedBalancedSignUpperH1Index67.index_pc h
      (GroupedBalancedSignUpperH1Header67.header_pc s pc))
  have hfirst := Keygen.ordinary_trans image s h i 14 18 htrace itrace
  have hall := Keygen.ordinary_trans image s i (prepared s) 32 6
    (by simpa only [Nat.reduceAdd] using hfirst) rtrace
  simpa only [Nat.reduceAdd] using hall

theorem prepared_pc (s : MachineState) (pc : s.pc = 0x17b0) :
    (prepared s).pc = 0x1848 := by
  exact GroupedBalancedSignUpperH1Ready67.ready_pc _
    (GroupedBalancedSignUpperH1Index67.index_pc _
      (GroupedBalancedSignUpperH1Header67.header_pc s pc))

private theorem header_math (base pair : Nat) :
    (1 : Word) + (BitVec.ofNat 64 base <<< 8) +
      (BitVec.ofNat 64 pair <<< 24) =
      KeygenDomain.header 1 base 0 pair 0 := by
  unfold KeygenDomain.header
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  rw [KeygenDomain.shift_ofNat, KeygenDomain.shift_ofNat]
  conv_rhs => rw [BitVec.ofNat_add]
  conv_rhs => rw [BitVec.ofNat_add]
  rfl

theorem prepared_header (s : MachineState) (base pair : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (pairWord : s.getMem 0x81030 = BitVec.ofNat 64 pair) :
    (prepared s).getMem 0x80000 =
      KeygenDomain.header 1 base 0 pair 0 := by
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  have hhead := GroupedBalancedSignUpperH1Header67.header_word s
  rw [level,pairWord] at hhead
  have ih := GroupedBalancedSignUpperH1Index67.index_frame h 0x80000
    (by decide) (by decide) (by decide)
  have rh := GroupedBalancedSignUpperH1Ready67.ready_frame i 0x80000
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem 0x80000 = _
  rw [rh, ih, hhead]
  exact header_math base pair

theorem prepared_index (s : MachineState) (leaf : Nat)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64) :
    ∀ j : Fin 3,
      (prepared s).getMem (Signing.wordAddress 0x80008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64 := by
  intro j
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  have ri := GroupedBalancedSignUpperH1Ready67.ready_frame i
    (Signing.wordAddress 0x80008 j.val)
  have iw := GroupedBalancedSignUpperH1Index67.index_words h j
  have hs := GroupedBalancedSignUpperH1Header67.header_frame s
    (Signing.wordAddress 0x81008 j.val) (by fin_cases j <;> decide)
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem _ = _
  rw [ri,iw,hs]
  exact address j

theorem prepared_key (s : MachineState) (secretKey : SecretKey)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        secretKey.extractLsb' (64*j.val) 64) :
    ∀ j : Fin 4,
      (prepared s).getMem (Signing.wordAddress 0x80020 j.val) =
        secretKey.extractLsb' (64*j.val) 64 := by
  intro j
  let h := GroupedBalancedSignUpperH1Header67.headerState s
  let i := GroupedBalancedSignUpperH1Index67.indexState h
  change (GroupedBalancedSignUpperH1Ready67.readyState i).getMem _ = _
  rw [GroupedBalancedSignUpperH1Ready67.ready_frame i _]
  rw [GroupedBalancedSignUpperH1Index67.index_frame h _
    (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    (by fin_cases j <;> decide)]
  rw [GroupedBalancedSignUpperH1Header67.header_frame s _
    (by fin_cases j <;> decide)]
  exact keyWords j

theorem secret_query (s : MachineState) (secretKey : SecretKey)
    (base leaf pair : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (pairWord : s.getMem 0x81030 = BitVec.ofNat 64 pair)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        secretKey.extractLsb' (64*j.val) 64) :
    hashInput (prepared s) =
      Reference.packed (KeygenDomain.secretPayload
        (KeygenDomain.header 1 base 0 pair 0) leaf secretKey) := by
  have args := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  apply KeygenDomain.secret_query_eq (prepared s) _ leaf secretKey
    args.1 args.2.1
  exact KeygenDomain.secret_words_of_layout (prepared s)
    (KeygenDomain.header 1 base 0 pair 0) leaf secretKey
    (prepared_header s base pair level pairWord)
    (prepared_index s leaf address)
    (prepared_key s secretKey keyWords)

theorem secret_answer (hash : Hash) (s : MachineState)
    (secretKey : SecretKey) (base leaf pair : Nat)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (pairWord : s.getMem 0x81030 = BitVec.ofNat 64 pair)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        secretKey.extractLsb' (64*j.val) 64) :
    ∀ j : Fin 4,
      (writeHash (prepared s) (hash (hashInput (prepared s)))).getMem
        (Signing.wordAddress 0x80300 j.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf pair).extractLsb'
          (64*j.val) 64 := by
  intro j
  have args := GroupedBalancedSignUpperH1Ready67.ready_regs
    (GroupedBalancedSignUpperH1Index67.indexState
      (GroupedBalancedSignUpperH1Header67.headerState s))
  rw [Signing.hash_answer_word (prepared s)
    (hash (hashInput (prepared s))) args.2.2.1 j]
  rw [secret_query s secretKey base leaf pair level pairWord address keyWords]
  rfl

theorem secret_call (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x17b0) :
    Trace hash image s 39 46 1 1
      (writeHash (prepared s) (hash (hashInput (prepared s)))) := by
  have steps := prepared_steps s pc
  have readyPc := prepared_pc s pc
  have code : fetch image (prepared s) = some (.base .ECALL) := by
    have raw : Keygen.instructionAt image 0x1848 = some (.base .ECALL) := by decide
    simpa only [Keygen.fetch_at, readyPc] using raw
  obtain ⟨source,bits,destination,service⟩ :=
    GroupedBalancedSignUpperH1Ready67.ready_regs
      (GroupedBalancedSignUpperH1Index67.indexState
        (GroupedBalancedSignUpperH1Header67.headerState s))
  have call := KeygenDomain.secret_hash_trace image hash (prepared s)
    code service source bits destination
  simpa only [Nat.reduceAdd] using
    (OrdinarySteps.trace (hash := hash) steps).trans call

#print axioms secret_query
#print axioms secret_answer
#print axioms secret_call
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Query67
