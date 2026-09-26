import SigGolfCandidate.Hypertree.SecurityVerifyCost

/-! Inlined from SigGolfCandidate.Hypertree.KeygenQueryAccounting; its only importer was SigGolfCandidate.Hypertree.SecurityBytecodeCounts. -/
section
namespace SigGolfCandidate.Hypertree.KeygenQueryAccounting
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp SecurityVerifyCost
set_option maxRecDepth 4096

theorem eval_query (hash : Hash) (input : Query) :
    evalWithAnswerFn hash (liftM (HashSpec.query input))=hash input := rfl

theorem calls_query (hash : Hash) (input : Query) :
    calls hash (liftM (HashSpec.query input))=1 := rfl

/-- Recorded interpreter calls count every actual H query, including cached repeats,
failed executions and unfinished observations. -/
theorem execute_calls (hash : Hash) (fuel : Nat) (image : Image) (state : MachineState) :
    calls hash (execute fuel image state) = (evalWithAnswerFn hash (execute fuel image state)).hashCalls := by
  induction fuel generalizing state with
  | zero => simp [execute]
  | succ fuel ih =>
    simp only [execute]
    split
    · simp
    · split
      · simp
      · split
        · simp only [calls_query,calls_bind,calls_pure,evalWithAnswerFn_bind,eval_query,
            evalWithAnswerFn_pure,Execution.charge,ih,Nat.zero_add,Nat.add_comm]
        · simp
    · split
      · simp
      · simp only [calls_map,evalWithAnswerFn_map,Execution.charge,ih,Nat.zero_add]

/-- Generic accounting for the organizer's actual typed loader, interpreter and decoder. -/
theorem run_calls (candidate : Submission) (hash : Hash) (phase : Phase) (input : Input candidate.sizes phase) :
    calls hash (candidate.run phase input) = (candidate.runWith hash phase input).hashCalls := by
  unfold Submission.runWith Submission.run
  split
  · simp
  · simp only [calls_bind,calls_pure,Nat.add_zero,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    exact execute_calls hash _ _ _

/-- info: 'SigGolfCandidate.Hypertree.KeygenQueryAccounting.run_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_calls

end SigGolfCandidate.Hypertree.KeygenQueryAccounting

end

namespace SigGolfCandidate.Hypertree.SecurityBytecodeCounts
open SigGolf OracleComp Reference SecurityVerifyCost
set_option maxRecDepth 4096

@[simp] theorem calls_secret (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    calls hash (SecurityReference.secret secretKey level tree side chain)=1 := by
  simp [SecurityReference.secret]

@[simp] theorem calls_endpoint (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (chain : Chain) :
    calls hash (SecurityReference.endpoint secretKey level tree side chain)=8 := by
  simp [SecurityReference.endpoint,calls_bind,calls_walk]

theorem calls_leafRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) :
    calls hash (SecurityReference.leafRoot secretKey level tree side)=(if level=0 then 2 else 369) := by
  by_cases zero : level=0
  · simp [SecurityReference.leafRoot,zero,calls_bind]
  · simp [SecurityReference.leafRoot,zero,calls_bind,calls_sequenceFin]

theorem calls_treeRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) :
    calls hash (SecurityReference.treeRoot secretKey level tree)=(if level=0 then 5 else 739) := by
  by_cases zero : level=0 <;> simp [SecurityReference.treeRoot,calls_bind,calls_leafRoot,zero]

/-- The monadic reference key generator has exactly the machine's 739 H queries. -/
theorem calls_keygen (hash : Hash) (secretKey : SecretKey) : calls hash (SecurityReference.keygen secretKey)=739 := by
  simp [SecurityReference.keygen,calls_treeRoot]

theorem calls_signChain (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool)
    (message : Digest) (chain : Chain) :
    calls hash (SecurityReference.signChain secretKey level tree side message chain)=8 := by
  simp only [SecurityReference.signChain,calls_bind,calls_secret,calls_walk,calls_pure,Nat.add_zero]
  have bound := (digit message chain).isLt
  omega

theorem calls_signLayerWithRoot (hash : Hash) (secretKey : SecretKey) (level tree : Nat) (side : Bool) (message : Digest) :
    calls hash (SecurityReference.signLayerWithRoot secretKey level tree side message)=(if level=0 then 5 else 739) := by
  by_cases zero : level=0 <;> cases side <;>
    simp [SecurityReference.signLayerWithRoot,zero,calls_bind,calls_leafRoot,calls_sequenceFin,calls_signChain]

theorem calls_signUpper (hash : Hash) (secretKey : SecretKey) (count level index : Nat) (message : Digest)
    (positive : 0<level) :
    calls hash (SecurityReference.signUpper secretKey count level index message)=739*count := by
  induction count generalizing level index message with
  | zero => simp [SecurityReference.signUpper]
  | succ count ih =>
    simp only [SecurityReference.signUpper,calls_bind,calls_signLayerWithRoot,
      if_neg (by omega : level ≠ 0),calls_pure,Nat.add_zero]
    rw [ih _ _ _ (by omega)]
    omega

theorem calls_randomizedIndex (hash : Hash) (secretKey : SecretKey) (message : Message) :
    calls hash (SecurityRandomOracle.randomizedIndex secretKey message)=2 := by
  simp [SecurityRandomOracle.randomizedIndex,calls_bind,KeygenQueryAccounting.calls_query]

/-- Shared chain work makes the full reference signer match the bytecode's exact H-call count. -/
theorem calls_signCompact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    calls hash (SecurityReference.signCompact secretKey message)=117508 := by
  simp only [SecurityReference.signCompact,calls_bind,calls_randomizedIndex,calls_signLayerWithRoot,
    calls_signUpper hash secretKey 159 1 _ _ (by decide),calls_pure]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.SecurityBytecodeCounts.calls_signCompact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms calls_signCompact

end SigGolfCandidate.Hypertree.SecurityBytecodeCounts
