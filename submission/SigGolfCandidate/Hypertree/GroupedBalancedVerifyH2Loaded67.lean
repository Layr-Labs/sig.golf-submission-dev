import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Entry67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizer67

/-! Exact loaded H2 query and the first sixteen bytes of its answer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Loaded67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem hash_code : Keygen.instructionAt image 0x1234 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

private theorem copy_setup_code : Keygen.CopySetupCode image 0x1238 0x300 0x500 2 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem copy_code : Keygen.CopyCode image 0x124c := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem loaded_query (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query,
      initialState program .verify input = some initial ∧
      Trace hash image initial 189 204 1 2 query ∧ query.pc = 0x1234 ∧
      query.getReg .x5 = 1 ∧ query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 384 ∧ query.getReg .x12 = 0x80300 ∧
      query.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,_,before,loaded,beforeTrace,beforePC,_,_,pointer⟩ :=
    GroupedBalancedVerifyH2InputCopy67.loaded_copy hash input
  let query := GroupedBalancedVerifyH2Entry67.setupState before
  have setupRun := GroupedBalancedVerifyH2Entry67.setup_steps before beforePC
  obtain ⟨service,src,len,dst⟩ := GroupedBalancedVerifyH2Entry67.setup_regs before
  refine ⟨initial,query,loaded,?_,GroupedBalancedVerifyH2Entry67.setup_pc before beforePC,
    service,src,len,dst,(GroupedBalancedVerifyH2Entry67.setup_pointer before).trans pointer⟩
  simpa only [Nat.reduceAdd] using beforeTrace.trans setupRun.trace

theorem loaded_output (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 207 229 2 3 final ∧ final.pc = 0x1264 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x80500 i.val) =
        (hash (hashInput query)).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,query,loaded,beforeTrace,queryPC,service,src,len,dst,pointer⟩ :=
    loaded_query hash input
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 384 src (by simpa using len) dst (by decide)
  have hlen : (hashInput query).1 = 384 := by
    simp [hashInput,len,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 1 := by
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 8 1 1 afterHash := by
    have hf : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,queryPC] using hash_code
    have raw := Trace.hash query afterHash 0 0 0 0 hf service valid
      (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1238 := by
    simpa [afterHash,answer,Keygen.hash_pc,queryPC] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,words,_,_,frame⟩ :=
    Keygen.copy_two image 0x1238 0x300 0x500 0x80300 0x80500
      copy_setup_code copy_code (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      afterHash afterPC
  refine ⟨initial,query,final,loaded,?_,by simpa using finalPC,?_,?_⟩
  · have composed := beforeTrace.trans (hashRun.trans copyRun.trace)
    simpa only [Nat.reduceAdd] using composed
  · intro i
    have result := Signing.hash_answer_word query answer dst
      (⟨i.val,by have h := i.isLt; omega⟩ : Fin 4)
    exact (words i).trans (by simpa [afterHash,answer] using result)
  · have hashPointer : afterHash.getMem 0x81048 = query.getMem 0x81048 := by
      exact Signing.hash_answer_frame query answer dst 0x81048
        (by intro i; fin_cases i <;> decide)
    have copyPointer : final.getMem 0x81048 = afterHash.getMem 0x81048 :=
      frame 0x81048 (by intro i; fin_cases i <;> decide)
    exact copyPointer.trans (hashPointer.trans pointer)

#print axioms loaded_query
#print axioms loaded_output
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Loaded67
