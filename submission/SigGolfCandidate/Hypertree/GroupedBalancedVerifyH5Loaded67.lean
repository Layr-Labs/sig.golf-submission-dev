import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Entry67

/-! The official verifier reaches and performs its first protected H5 hash query. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Loaded67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem hash_code : Keygen.instructionAt image 0x1110 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem loaded_query (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query,
      initialState program .verify input = some initial ∧
      Trace hash image initial 104 104 0 0 query ∧
      query.pc = 0x1110 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 896 ∧
      query.getReg .x12 = 0x80300 ∧
      query.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,before,loaded,firstTrace,beforePC,pointer⟩ :=
    GroupedBalancedVerifySecondCopy67.from_loaded hash input
  let query := GroupedBalancedVerifyH5Entry67.setupState before
  have queryRun := GroupedBalancedVerifyH5Entry67.setup_steps before beforePC
  obtain ⟨service,src,len,dst⟩ := GroupedBalancedVerifyH5Entry67.setup_regs before
  refine ⟨initial,query,loaded,?_,GroupedBalancedVerifyH5Entry67.setup_pc before beforePC,
    service,src,len,dst,(GroupedBalancedVerifyH5Entry67.setup_pointer before).trans pointer⟩
  simpa only [Nat.reduceAdd] using firstTrace.trans queryRun.trace

theorem loaded_first_hash (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 105 120 1 2 final ∧ final.pc = 0x1114 := by
  obtain ⟨initial,query,loaded,runPrefix,pc,service,src,len,dst,_⟩ :=
    loaded_query hash input
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 896 src (by simpa using len) dst (by decide)
  have hlen : (hashInput query).1 = 896 := by
    simp [hashInput,len,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 2 := by
    rw [hlen]
    decide
  let final := writeHash query (hash (hashInput query))
  have single : Trace hash image query 1 16 1 2 final := by
    have hf : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,pc] using hash_code
    have raw := Trace.hash query final 0 0 0 0 hf service valid (Trace.refl final)
    simpa [hcomp,final] using raw
  refine ⟨initial,final,loaded,?_,?_⟩
  · simpa only [Nat.reduceAdd] using runPrefix.trans single
  · simpa [final,Keygen.hash_pc,pc] using Keygen.hash_pc query (hash (hashInput query))

#print axioms loaded_query
#print axioms loaded_first_hash
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Loaded67
