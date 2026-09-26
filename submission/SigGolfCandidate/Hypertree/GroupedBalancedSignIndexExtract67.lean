import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrefix67
import SigGolfCandidate.Hypertree.KeygenTrace

/-! Copy the signer's tag5 H5 answer into its 160-bit index state. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtract67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 0x90)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x11a8 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x11ac = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x11b0 = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x11b4 = some (.base (.ADDI .x7 .x7 0x90)) ∧
    Keygen.instructionAt image 0x11b8 = some (.base (.ADDI .x10 .x0 2)) := by
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x11a8) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x90)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x11ac := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x11b0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x90)) 1
  · have hp : s3.pc = 0x11b4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x11b8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem copy_code : Keygen.CopyCode image 0x11bc := by decide

theorem copy_invariant (s : MachineState) (pc : s.pc = 0x11a8) :
    Keygen.CopyInvariant 0x11bc 0x80300 0x81090 2 2 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem copy_low (s : MachineState) (pc : s.pc = 0x11a8) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x11d4 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x81090 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x81090 i) →
        final.getMem a = s.getMem a) := by
  let begun := setupState s
  obtain ⟨final, loop, done, words, frame⟩ := Signing.copy_all image
    0x11bc copy_code 0x80300 0x81090 2 begun (copy_invariant s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ?_, done.2.2.1, ?_, ?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (setup_steps s pc) loop
    simpa only [show 12 + 5 = 17 by decide] using full
  · intro i hi
    rw [words i hi]
    simp [begun,setupState,execInstrBr]
  · intro a outside
    rw [frame a outside]
    simp [begun,setupState,execInstrBr]

def storeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x310)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x6 .x6 32)
  let s := execInstrBr s (.SRLI .x6 .x6 32)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xa0)
  execInstrBr s (.SD .x28 .x6 0)

private theorem store_code :
    Keygen.instructionAt image 0x11d4 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x11d8 = some (.base (.ADDI .x28 .x28 0x310)) ∧
    Keygen.instructionAt image 0x11dc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x11e0 = some (.base (.SLLI .x6 .x6 32)) ∧
    Keygen.instructionAt image 0x11e4 = some (.base (.SRLI .x6 .x6 32)) ∧
    Keygen.instructionAt image 0x11e8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x11ec = some (.base (.ADDI .x28 .x28 0xa0)) ∧
    Keygen.instructionAt image 0x11f0 = some (.base (.SD .x28 .x6 0)) := by
  decide

theorem store_steps (s : MachineState) (pc : s.pc = 0x11d4) :
    OrdinarySteps image s 8 (storeState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x310)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x6 .x6 32)
  let s5 := execInstrBr s4 (.SRLI .x6 .x6 32)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0xa0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := store_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x310)) 6
  · have hp : s1.pc = 0x11d8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x11dc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x6 .x6 32)) 4
  · have hp : s3.pc = 0x11e0 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x6 .x6 32)) 3
  · have hp : s4.pc = 0x11e4 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s5.pc = 0x11e8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0xa0)) 1
  · have hp : s6.pc = 0x11ec := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (storeState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s7.pc = 0x11f0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,storeState,ordinaryStep,
      memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,
      MEMORY_BYTES,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem store_pc (s : MachineState) (pc : s.pc = 0x11d4) :
    (storeState s).pc = 0x11f4 := by
  simp [storeState,execInstrBr,pc]

theorem store_high (s : MachineState) :
    (storeState s).getMem 0x810a0 =
      ((s.getMem 0x80310 <<< 32) >>> 32) := by
  simp [storeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem store_low (s : MachineState) (i : Fin 2) :
    (storeState s).getMem (Signing.wordAddress 0x81090 i.val) =
      s.getMem (Signing.wordAddress 0x81090 i.val) := by
  fin_cases i <;>
    simp [storeState,Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem store_frame (s : MachineState) (a : Word) (outside : a ≠ 0x810a0) :
    (storeState s).getMem a = s.getMem a := by
  change a ≠ 528544#64 at outside
  simp [storeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,outside]

theorem extract_answer (s : MachineState) (answer : BitVec 256)
    (pc : s.pc = 0x11a8)
    (words : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80300 i.val) =
        answer.extractLsb' (64*i.val) 64) :
    ∃ final, OrdinarySteps image s 25 final ∧ final.pc = 0x11f4 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x81090 i.val) =
          answer.extractLsb' (64*i.val) 64) ∧
      final.getMem 0x810a0 =
        ((answer.extractLsb' 128 64 <<< 32) >>> 32) ∧
      (∀ i : Fin 4, final.getMem (Signing.wordAddress 0x20 i.val) =
        s.getMem (Signing.wordAddress 0x20 i.val)) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0x20060 ≤ a.toNat → a.toNat < 0x20080 →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,copyPath,copyPC,lowWords,copyFrame⟩ := copy_low s pc
  let final := storeState copied
  refine ⟨final,?_,store_pc copied copyPC,?_,?_,?_,?_,?_⟩
  · have path := Keygen.ordinary_trans image s copied final 17 8
      copyPath (store_steps copied copyPC)
    simpa only [Nat.reduceAdd] using path
  · intro i
    rw [store_low copied i,lowWords i.val i.isLt]
    exact words ⟨i.val,by have := i.isLt; omega⟩
  · rw [store_high]
    have outside : ∀ i, i < 2 →
        (0x80310 : Word) ≠ Signing.wordAddress 0x81090 i := by
      intro i hi
      interval_cases i <;> decide
    rw [copyFrame 0x80310 outside]
    exact congrArg (fun word : Word => (word <<< 32) >>> 32)
      (words ⟨2,by decide⟩)
  · intro i
    have outsideStore : Signing.wordAddress 0x20 i.val ≠ 0x810a0 := by
      fin_cases i <;> decide
    rw [store_frame copied _ outsideStore]
    apply copyFrame
    intro j hj
    fin_cases i <;> interval_cases j <;> decide
  · intro a high
    have outsideStore : a ≠ 0x810a0 := by
      intro eq
      subst a
      exact (show ¬ 0xfff700 ≤ (0x810a0 : Word).toNat from by decide) high
    rw [store_frame copied a outsideStore]
    apply copyFrame
    intro i hi
    have ne := Signing.outside_copy_word a.toNat 0x81090 2 i
      a.isLt (by decide) hi (Or.inr (by omega))
    simpa using ne
  · intro a low high
    have outsideStore : a ≠ 0x810a0 := by
      intro eq
      subst a
      exact (show ¬ (0x810a0 : Word).toNat < 0x20080 from by decide) high
    rw [store_frame copied a outsideStore]
    apply copyFrame
    intro i hi
    have ne := Signing.outside_copy_word a.toNat 0x81090 2 i
      a.isLt (by decide) hi (Or.inl (by omega))
    simpa using ne

#print axioms copy_low
#print axioms store_steps
#print axioms store_high
#print axioms extract_answer

end SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtract67
