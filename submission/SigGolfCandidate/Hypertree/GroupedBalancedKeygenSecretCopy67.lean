import SigGolfCandidate.Hypertree.GroupedBalancedKeygenBranch67
import SigGolfCandidate.Hypertree.KeygenCopyX19

/-! The key generator copies the 32-byte secret key into its seed buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedKeygenImage67.image

def prepareState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SRLI .x6 .x19 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 32)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 32)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem prepare_code :
    Keygen.instructionAt image 0x1068 = some (.base (.SRLI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x106c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1070 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1074 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1078 = some (.base (.ADDI .x6 .x0 32)) ∧
    Keygen.instructionAt image 0x107c = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1080 = some (.base (.ADDI .x7 .x7 32)) ∧
    Keygen.instructionAt image 0x1084 = some (.base (.ADDI .x10 .x0 4)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem prepare_steps (s : MachineState) (pc : s.pc = 0x1068) :
    OrdinarySteps image s 8 (prepareState s) := by
  let s1 := execInstrBr s (.SRLI .x6 .x19 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 48)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 32)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 32)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := prepare_code
  apply OrdinarySteps.step s s1 _ (.base (.SRLI .x6 .x19 1)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s1.pc = 0x106c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 48)) 5
  · have hp : s2.pc = 0x1070 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s3.pc = 0x1074 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 32)) 3
  · have hp : s4.pc = 0x1078 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s5.pc = 0x107c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 32)) 1
  · have hp : s6.pc = 0x1080 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (prepareState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s7.pc = 0x1084 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem prepare_fields (s : MachineState) (pc : s.pc = 0x1068) :
    (prepareState s).pc = 0x1088 ∧
    (prepareState s).getReg .x6 = 0x20 ∧
    (prepareState s).getReg .x7 = 0x80020 ∧
    (prepareState s).getReg .x10 = 4 := by
  simp [prepareState,execInstrBr,pc,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem prepare_mem_other (s : MachineState) (a : Word)
    (hne : a ≠ 0x81030) :
    (prepareState s).getMem a = s.getMem a := by
  simp [prepareState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro same
  exact False.elim (hne same)

theorem secret_copy_code : Keygen.CopyCode image 0x1088 := by
  unfold Keygen.CopyCode image GroupedBalancedKeygenImage67.image
  decide

theorem secret_copy_frame (s : MachineState) (pc : s.pc = 0x1068) :
    ∃ final, OrdinarySteps image s 32 final ∧
      final.pc = 0x10a0 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) ∧
      (∀ a, (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = (prepareState s).getMem a) ∧
      final.getReg .x19 = s.getReg .x19 := by
  let ready := prepareState s
  obtain ⟨readyPC,readySrc,readyDst,readyCount⟩ := prepare_fields s pc
  have readyInv : Keygen.CopyInvariant 0x1088 0x20 0x80020 4 4 ready := by
    refine ⟨by decide,by decide,?_,readySrc,readyDst,readyCount⟩
    simpa [ready] using readyPC
  obtain ⟨final,copied,done,words,frame,x19⟩ :=
    KeygenCopyX19.copy_all_x19 image 0x1088 secret_copy_code
      0x20 0x80020 4 ready readyInv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have pre := prepare_steps s pc
  refine ⟨final,?_,?_,?_,frame,?_⟩
  · simpa only [Nat.reduceMul,Nat.reduceAdd] using
      Keygen.ordinary_trans image s ready final 8 (6*4) pre copied
  · simpa [Keygen.CopyInvariant] using done.2.2.1
  · intro i hi
    rw [words i hi,prepare_mem_other s (Signing.wordAddress 0x20 i) ?_]
    intro same
    have hn := congrArg BitVec.toNat same
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x20+8*i < 2^64)] at hn
    have hc : (0x81030 : Word).toNat = 0x81030 := by decide
    rw [hc] at hn
    omega
  · rw [x19]
    change (prepareState s).getReg .x19 = s.getReg .x19
    simp [prepareState,execInstrBr,MachineState.getReg_setReg_ne]

theorem secret_copy (s : MachineState) (pc : s.pc = 0x1068) :
    ∃ final, OrdinarySteps image s 32 final ∧
      final.pc = 0x10a0 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) := by
  obtain ⟨final,steps,done,words,_,_⟩ := secret_copy_frame s pc
  exact ⟨final,steps,done,words⟩

private theorem source_word_low (i : Nat) (hi : i < 4) :
    (Signing.wordAddress 0x20 i).toNat < 0x100 := by
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x20+8*i < 2^64)]
  omega

private theorem source_word_ne (i : Nat) (hi : i < 4)
    (a : Word) (high : 0x81000 ≤ a.toNat) :
    Signing.wordAddress 0x20 i ≠ a := by
  intro same
  have hn := congrArg BitVec.toNat same
  have low := source_word_low i hi
  omega

theorem entry_source_word (s : MachineState) (i : Nat) (hi : i < 4) :
    (GroupedBalancedKeygenPrefix67.entryState s).getMem
      (Signing.wordAddress 0x20 i) =
      s.getMem (Signing.wordAddress 0x20 i) := by
  apply GroupedBalancedKeygenPrefix67.entry_mem_other
  · exact source_word_ne i hi 0x81000 (by decide)
  · exact source_word_ne i hi 0x81008 (by decide)
  · exact source_word_ne i hi 0x81010 (by decide)
  · exact source_word_ne i hi 0x81018 (by decide)
  · exact source_word_ne i hi 0x81030 (by decide)

/-- The concrete keygen prefix reaches the first secret-seed preparation with
the four loaded secret-key words copied byte-for-byte. -/
theorem initial_secret_copy (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    ∃ final, Trace hash image s 57 57 0 0 final ∧
      final.pc = 0x10a0 ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x20 i)) := by
  let entered := GroupedBalancedKeygenPrefix67.entryState s
  let branched := GroupedBalancedKeygenBranch67.branchState entered
  obtain ⟨first,firstPC⟩ := GroupedBalancedKeygenBranch67.initial_branch_trace
    hash s pc
  obtain ⟨final,second,secondPC,words⟩ := secret_copy branched firstPC
  refine ⟨final,?_,secondPC,?_⟩
  · simpa only [image,GroupedBalancedKeygenBranch67.image,
      Nat.reduceAdd] using first.trans second.trace
  · intro i hi
    rw [words i hi,GroupedBalancedKeygenBranch67.branch_mem,
      entry_source_word s i hi]

#print axioms secret_copy
#print axioms initial_secret_copy

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenSecretCopy67
