import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Query67
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! Copy the first H4 answer into the running tree root buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Answer67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem setup_code : Keygen.CopySetupCode image 0x146c 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem copy_code : Keygen.CopyCode image 0x1480 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem answer_copy (s : MachineState) (pc : s.pc = 0x146c) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1498 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
      final.getMem 0x81048 = s.getMem 0x81048 ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s final := by
  obtain ⟨final,run,endPC,words,_,sp,frame⟩ :=
    Keygen.copy_two image 0x146c 0x300 0x500 0x80300 0x80500
      setup_code copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using endPC,words,?_,?_,?_,sp⟩
  · exact frame 0x81048 (by intro i; fin_cases i <;> decide)
  · exact frame 0x81050 (by intro i; fin_cases i <;> decide)
  · intro a ha
    apply frame a
    intro i
    fin_cases i <;> intro eq <;>
      have hn := congrArg BitVec.toNat eq <;>
      simp [Signing.wordAddress] at hn <;> omega

theorem loaded_answer (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n final,
      initialState program .verify input = some initial ∧
      (n = 357 ∨ n = 358) ∧
      Trace hash image initial n (n+29) 3 4 final ∧
      final.pc = 0x1498 ∧ final.getMem 0x81048 = 0x2c730 := by
  obtain ⟨initial,n,before,loaded,ncases,beforeRun,beforePC,pointer⟩ :=
    GroupedBalancedVerifyTreeH4Query67.loaded_hash hash input
  obtain ⟨final,copyRun,copyPC,_,copyPointer,_,_⟩ := answer_copy before beforePC
  refine ⟨initial,n+17,final,loaded,?_,?_,copyPC,copyPointer.trans pointer⟩
  · rcases ncases with h | h <;> simp [h]
  · have run := beforeRun.trans copyRun.trace
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

#print axioms answer_copy
#print axioms loaded_answer
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Answer67
