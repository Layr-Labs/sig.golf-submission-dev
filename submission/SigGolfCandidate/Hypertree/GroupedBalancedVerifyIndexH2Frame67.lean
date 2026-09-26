import SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexPrelude67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Loaded67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Setup67
import SigGolfCandidate.Hypertree.KeygenDomain

/-! The bottom-leaf H2 query preserves the three H5 index words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexH2Frame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

private theorem input_setup_code : Keygen.CopySetupCode image
    0x1184 0x510 0x20 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem input_copy_code : Keygen.CopyCode image 0x1198 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem output_setup_code : Keygen.CopySetupCode image
    0x1238 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem output_copy_code : Keygen.CopyCode image 0x124c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

private theorem hash_code : Keygen.instructionAt image 0x1234 =
    some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

def IndexFrame (s t : MachineState) : Prop :=
  ∀ i : Fin 3,
    t.getMem (Signing.wordAddress 0x81008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val)

theorem IndexFrame.trans {s t u : MachineState}
    (first : IndexFrame s t) (second : IndexFrame t u) :
    IndexFrame s u := by
  intro i
  exact (second i).trans (first i)

theorem input_copy_index (s : MachineState) (pc : s.pc = 0x1184) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x11b0 ∧
      IndexFrame s final := by
  obtain ⟨final,run,finalPC,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1184 0x510 0x20 0x80510 0x80020
      input_setup_code input_copy_code
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using finalPC,?_⟩
  intro i
  exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)

theorem h2_setup_index (s : MachineState) :
    IndexFrame s (GroupedBalancedVerifyH2Entry67.setupState s) := by
  exact GroupedBalancedVerifyH2Setup67.setup_index_frame s

theorem output_copy_index (s : MachineState) (pc : s.pc = 0x1238) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1264 ∧
      IndexFrame s final := by
  obtain ⟨final,run,finalPC,_,_,_,frame⟩ :=
    Keygen.copy_two image 0x1238 0x300 0x500 0x80300 0x80500
      output_setup_code output_copy_code
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s pc
  refine ⟨final,run,by simpa using finalPC,?_⟩
  intro i
  exact frame _ (by intro j; fin_cases i <;> fin_cases j <;> decide)

theorem h2_hash_trace (hash : Hash) (query : MachineState)
    (pc : query.pc = 0x1234)
    (service : query.getReg .x5 = 1)
    (src : query.getReg .x10 = 0x80000)
    (len : query.getReg .x11 = 384)
    (dst : query.getReg .x12 = 0x80300) :
    Trace hash image query 1 8 1 1
      (writeHash query (hash (hashInput query))) := by
  have fetched : fetch image query = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at,pc] using hash_code
  exact KeygenDomain.hash_trace image hash query fetched service src len dst

theorem h2_index_frame (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1184) :
    ∃ final, Trace hash image s 68 75 1 1 final ∧
      final.pc = 0x1264 ∧ IndexFrame s final := by
  obtain ⟨copied,copyRun,copyPC,copyFrame⟩ := input_copy_index s pc
  let query := GroupedBalancedVerifyH2Entry67.setupState copied
  have queryRun := GroupedBalancedVerifyH2Entry67.setup_steps copied copyPC
  have queryPC := GroupedBalancedVerifyH2Entry67.setup_pc copied copyPC
  obtain ⟨service,src,len,dst⟩ :=
    GroupedBalancedVerifyH2Entry67.setup_regs copied
  let afterHash := writeHash query (hash (hashInput query))
  have hashRun : Trace hash image query 1 8 1 1 afterHash :=
    h2_hash_trace hash query queryPC service src len dst
  have hashPC : afterHash.pc = 0x1238 := by
    calc
      afterHash.pc = query.pc + 4 :=
        Keygen.hash_pc query (hash (hashInput query))
      _ = 0x1238 := by rw [queryPC]; decide
  obtain ⟨final,outRun,finalPC,outFrame⟩ :=
    output_copy_index afterHash hashPC
  refine ⟨final,?_,finalPC,?_⟩
  · have all := ((copyRun.trace (hash := hash)).trans queryRun.trace).trans
      (hashRun.trans outRun.trace)
    simpa only [Nat.reduceAdd] using all
  · have hashFrame : IndexFrame query afterHash := by
      intro i
      exact Signing.hash_answer_frame query (hash (hashInput query))
        dst _ (by intro j; fin_cases i <;> fin_cases j <;> decide)
    exact copyFrame.trans ((h2_setup_index copied).trans
      (hashFrame.trans outFrame))

#print axioms h2_index_frame
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexH2Frame67
