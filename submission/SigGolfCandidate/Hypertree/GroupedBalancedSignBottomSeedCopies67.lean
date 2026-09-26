import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2Prelude67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2Query67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSeedCopies67. -/
section
/-! The signer's bottom H2 call hashes the just-derived 16-byte seed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev prelude := GroupedBalancedSignBottomH2Prelude67.preludeState

theorem leaf_words (staged : MachineState) (leaf : Nat)
    (seed : Reference.Digest)
    (level : staged.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 6, (prelude staged).getMem
      (Signing.wordAddress 0x80000 i.val) =
        KeygenDomain.inputWord (KeygenDomain.header 2 0 0 0 0)
          leaf seed i := by
  let ready := prelude staged
  have header : ready.getMem 0x80000 = KeygenDomain.header 2 0 0 0 0 := by
    have h := GroupedBalancedSignBottomH2Prelude67.prelude_header staged (0 : Fin 4)
    rw [level] at h
    simpa [ready,Signing.wordAddress,KeygenDomain.header] using h
  have indexWords : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH2Prelude67.prelude_header staged (1 : Fin 4)).trans (address 0)
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH2Prelude67.prelude_header staged (2 : Fin 4)).trans (address 1)
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH2Prelude67.prelude_header staged (3 : Fin 4)).trans (address 2)
  have valueWords : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomH2Prelude67.prelude_frame staged _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact seedWords i
  exact KeygenDomain.words_of_layout ready
    (KeygenDomain.header 2 0 0 0 0) leaf seed
    header indexWords valueWords

theorem leaf_query (staged : MachineState) (leaf : Nat)
    (seed : Reference.Digest)
    (level : staged.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    hashInput (prelude staged) =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 0 0 0 0) leaf seed) := by
  obtain ⟨source,bits,_,_⟩ :=
    GroupedBalancedSignBottomH2Prelude67.prelude_hash_args staged
  exact KeygenDomain.query_eq (prelude staged)
    (KeygenDomain.header 2 0 0 0 0) leaf seed source bits
    (leaf_words staged leaf seed level address seedWords)

theorem leaf_answer (hash : Hash) (staged : MachineState)
    (leaf : Nat) (seed : Reference.Digest)
    (level : staged.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.leafFromSeed hash leaf seed).extractLsb'
          (64*i.val) 64 := by
  obtain ⟨source,bits,destination,_⟩ :=
    GroupedBalancedSignBottomH2Prelude67.prelude_hash_args staged
  have words := leaf_words staged leaf seed level address seedWords
  intro i
  simpa only [GroupedBottomTree.leafFromSeed] using
    (KeygenDomain.answer_words hash (prelude staged)
      2 0 leaf 0 0 0 seed source bits destination words i)

theorem leaf_call (hash : Hash) (staged : MachineState)
    (pc : staged.pc = 0x13f0) :
    Trace hash image staged 34 41 1 1
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))) := by
  have steps := GroupedBalancedSignBottomH2Prelude67.prelude_steps staged pc
  have readyPc := GroupedBalancedSignBottomH2Prelude67.prelude_pc staged pc
  have code : fetch image (prelude staged) = some (.base .ECALL) := by
    have raw : Keygen.instructionAt image 0x1474 = some (.base .ECALL) := by decide
    simpa only [Keygen.fetch_at,readyPc] using raw
  obtain ⟨source,bits,destination,service⟩ :=
    GroupedBalancedSignBottomH2Prelude67.prelude_hash_args staged
  have call := KeygenDomain.hash_trace image hash (prelude staged)
    code service source bits destination
  simpa only [Nat.reduceAdd,image,
    GroupedBalancedSignBottomH2Prelude67.image] using
    (OrdinarySteps.trace (hash := hash) steps).trans call

#print axioms leaf_words
#print axioms leaf_query
#print axioms leaf_answer
#print axioms leaf_call
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH2Query67

end

/-! The optional witness seed copy and mandatory H2 seed-input copy. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSeedCopies67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def selectedSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x20)
  let s := execInstrBr s (.ADDI .x7 .x7 0x80)
  execInstrBr s (.ADDI .x10 .x0 2)
private theorem selected_setup_code :
    Keygen.instructionAt image 0x1398 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x139c = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x13a0 = some (.base (.LUI .x7 0x20)) ∧
    Keygen.instructionAt image 0x13a4 = some (.base (.ADDI .x7 .x7 0x80)) ∧
    Keygen.instructionAt image 0x13a8 = some (.base (.ADDI .x10 .x0 2)) := by
  decide
theorem selected_setup_steps (s : MachineState) (pc : s.pc = 0x1398) :
    OrdinarySteps image s 5 (selectedSetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x20)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x80)
  obtain ⟨c0,c1,c2,c3,c4⟩ := selected_setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x139c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x20)) 2
  · have hp : s2.pc = 0x13a0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x80)) 1
  · have hp : s3.pc = 0x13a4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (selectedSetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x13a8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem selected_copy_code : Keygen.CopyCode image 0x13ac := by decide
theorem selected_copy_inv (s : MachineState) (pc : s.pc = 0x1398) :
    Keygen.CopyInvariant 0x13ac 0x80300 0x20080 2 2 (selectedSetup s) := by
  unfold Keygen.CopyInvariant selectedSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem selected_copy (s : MachineState) (pc : s.pc = 0x1398) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x13c4 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x20080 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x20080 i) →
        final.getMem a = s.getMem a) := by
  let begun := selectedSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x13ac selected_copy_code 0x80300 0x20080 2 begun
    (selected_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (selected_setup_steps s pc) loop
    simpa only [show 12 + 5 = 17 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,selectedSetup,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,selectedSetup,execInstrBr]

def inputSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 2)
private theorem input_setup_code :
    Keygen.instructionAt image 0x13c4 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x13c8 = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x13cc = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x13d0 = some (.base (.ADDI .x7 .x7 0x20)) ∧
    Keygen.instructionAt image 0x13d4 = some (.base (.ADDI .x10 .x0 2)) := by
  decide
theorem input_setup_steps (s : MachineState) (pc : s.pc = 0x13c4) :
    OrdinarySteps image s 5 (inputSetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x20)
  obtain ⟨c0,c1,c2,c3,c4⟩ := input_setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x13c8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x13cc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · have hp : s3.pc = 0x13d0 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (inputSetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x13d4 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _
theorem input_copy_code : Keygen.CopyCode image 0x13d8 := by decide
theorem input_copy_inv (s : MachineState) (pc : s.pc = 0x13c4) :
    Keygen.CopyInvariant 0x13d8 0x80300 0x80020 2 2 (inputSetup s) := by
  unfold Keygen.CopyInvariant inputSetup
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]
theorem input_copy (s : MachineState) (pc : s.pc = 0x13c4) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x13f0 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let begun := inputSetup s
  obtain ⟨final,loop,done,words,frame⟩ := Signing.copy_all image
    0x13d8 input_copy_code 0x80300 0x80020 2 begun
    (input_copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (input_setup_steps s pc) loop
    simpa only [show 12 + 5 = 17 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,inputSetup,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,inputSetup,execInstrBr]

#print axioms selected_copy
#print axioms input_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSeedCopies67
