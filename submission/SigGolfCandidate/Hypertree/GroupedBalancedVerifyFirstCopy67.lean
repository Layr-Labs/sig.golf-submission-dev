import SigGolfCandidate.Hypertree.GroupedBalancedVerifySetup67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

/-! The verifier's first generated copy loop moves four input words into H5 scratch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyFirstCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

private theorem copy_code : Keygen.CopyCode image 0x1074 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem first_copy (s : MachineState)
    (pc : s.pc = 0x1074)
    (src : s.getReg .x6 = 0)
    (dst : s.getReg .x7 = 0x80030)
    (count : s.getReg .x10 = 4) :
    ∃ final, OrdinarySteps image s 24 final ∧
      final.pc = 0x108c ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80030 i) =
        s.getMem (Signing.wordAddress 0 i)) ∧
      (∀ a, (∀ i, i < 4 → a ≠ Signing.wordAddress 0x80030 i) →
        final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 := by
  have inv : Keygen.CopyInvariant 0x1074 0 0x80030 4 4 s := by
    simp [Keygen.CopyInvariant,pc,src,dst,count]
  obtain ⟨final,run,done,words,frame,_,sp⟩ :=
    Keygen.copy_all_frame image 0x1074 copy_code 0 0x80030 4 s inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  exact ⟨final,run,by simpa using endPC,words,frame,sp⟩

theorem from_setup (s : MachineState) (pc : s.pc = 0x1030) :
    ∃ final, OrdinarySteps image s 41 final ∧ final.pc = 0x108c ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80030 i) =
        (GroupedBalancedVerifySetup67.setupState s).getMem (Signing.wordAddress 0 i)) ∧
      final.getMem 0x81048 = 0x2c720 := by
  let setup := GroupedBalancedVerifySetup67.setupState s
  have setupRun := GroupedBalancedVerifySetup67.setup_steps s pc
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifySetup67.setup_regs s
  obtain ⟨final,copyRun,endPC,words,frame,_⟩ := first_copy setup
    (GroupedBalancedVerifySetup67.setup_pc s pc) src dst count
  refine ⟨final,?_,endPC,words,?_⟩
  · simpa only [Nat.reduceAdd] using Keygen.ordinary_trans image s setup final
      17 24 setupRun copyRun
  · have outside : ∀ i, i < 4 → (0x81048 : Word) ≠
        Signing.wordAddress 0x80030 i := by
      intro i hi
      interval_cases i <;> decide
    exact (frame 0x81048 outside).trans
      (GroupedBalancedVerifySetup67.setup_pointer s)

theorem from_loaded (hash : Hash)
    (input : Input GroupedBalancedProgram67Byte.submission.sizes .verify) :
    ∃ initial final,
      initialState GroupedBalancedProgram67Byte.submission .verify input = some initial ∧
      Trace hash image initial 53 53 0 0 final ∧ final.pc = 0x108c ∧
      (∀ i, i < 4 → final.getMem (Signing.wordAddress 0x80030 i) =
        (GroupedBalancedVerifySetup67.setupState
          (GroupedBalancedVerifyEntry67.entryState initial)).getMem
          (Signing.wordAddress 0 i)) ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,entry,loaded,entryTrace,entryPC,_,_,_,_,_⟩ :=
    GroupedBalancedVerifyEntry67.loaded_entry hash input
  obtain ⟨final,copyTrace,finalPC,words,pointer⟩ := from_setup entry entryPC
  obtain ⟨other,otherLoaded,otherPC⟩ := initialState_exists
    GroupedBalancedProgram67Byte.submission
    GroupedBalancedProgram67Byte.admissible .verify input
  rw [loaded] at otherLoaded
  have sameInitial : other = initial := Option.some.inj otherLoaded.symm
  subst other
  have canonical := (GroupedBalancedVerifyEntry67.entry_steps initial otherPC).trace
    (hash := hash)
  have sameEntry : entry = GroupedBalancedVerifyEntry67.entryState initial :=
    Trace.deterministic entryTrace canonical
  refine ⟨initial,final,loaded,?_,finalPC,?_,pointer⟩
  · simpa only [Nat.reduceAdd] using entryTrace.trans copyTrace.trace
  · simpa only [sameEntry] using words

#print axioms from_setup
#print axioms from_loaded
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyFirstCopy67
