import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Prelude67
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! The two sibling words are copied into the H2 input block. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2InputCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem setup_code : Keygen.CopySetupCode image 0x1184 0x510 0x20 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem copy_code : Keygen.CopyCode image 0x1198 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem input_copy (s : MachineState) (pc : s.pc = 0x1184) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x11b0 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (Signing.wordAddress 0x80510 i.val)) ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  obtain ⟨final,run,endPC,words,_,_,frame⟩ :=
    Keygen.copy_two image 0x1184 0x510 0x20 0x80510 0x80020
      setup_code copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using endPC,words,?_⟩
  exact frame 0x81048 (by intro i; fin_cases i <;> decide)

theorem loaded_copy (hash : Hash) (input : Input program.sizes .verify) :
    ∃ (initial before final : MachineState),
      initialState program .verify input = some initial ∧
      Trace hash image initial 156 171 1 2 final ∧ final.pc = 0x11b0 ∧
      final.getMem 0x80020 = before.getMem 0x2c720 ∧
      final.getMem 0x80028 = before.getMem 0x2c728 ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,before,staged,loaded,prefixRun,pc,low,high,pointer⟩ :=
    GroupedBalancedVerifyH2Prelude67.loaded_prelude hash input
  obtain ⟨final,copyRun,finalPC,words,frame⟩ := input_copy staged pc
  refine ⟨initial,before,final,loaded,?_,finalPC,?_,?_,frame.trans pointer⟩
  · simpa only [Nat.reduceAdd] using prefixRun.trans copyRun.trace
  · exact (words 0).trans low
  · exact (words 1).trans high

#print axioms loaded_copy
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2InputCopy67
