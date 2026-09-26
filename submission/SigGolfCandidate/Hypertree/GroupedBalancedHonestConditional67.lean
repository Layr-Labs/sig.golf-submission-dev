import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRunFunctional67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRunWire67
import SigGolfCandidate.Hypertree.GroupedBalancedExpandCopy67
import SigGolfCandidate.Hypertree.KeygenOrganizerBridges

/-! The honest full-track obligations now depend only on the verifier. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedHonestConditional67
open SigGolf OracleComp KeygenOrganizer
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission
private abbrev publicKey (hash : Hash) (secretKey : SecretKey) :=
  GroupedBalancedScheme67.keygen hash secretKey
private abbrev signature (hash : Hash) (secretKey : SecretKey)
    (message : Message) :=
  GroupedBalancedWire67.wire
    (GroupedBalancedScheme67.sign hash secretKey message)

def HonestVerifier (C : Nat) : Prop :=
  ∀ hash : Hash, ∀ secretKey : SecretKey, ∀ message : Message,
    ∃ cycles calls blocks : Nat,
      cycles ≤ C ∧
      submission.runWith hash .verify
        (message,publicKey hash secretKey,
          signature hash secretKey message) =
        ⟨some (),true,cycles,calls,blocks⟩

private theorem pipeline_success {σ ω : Type} (hash : Hash)
    (keygen : OracleComp HashSpec (RunResult (PublicKey × Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit))
    (pk : PublicKey) (cache : Cache) (signature : σ) (witness : ω)
    (kc kh kb sc sh sb ec eh eb vc vh vb : Nat)
    (kg : evalWithAnswerFn hash keygen = ⟨some (pk,cache),true,kc,kh,kb⟩)
    (sg : evalWithAnswerFn hash (sign pk cache) = ⟨some signature,true,sc,sh,sb⟩)
    (ex : evalWithAnswerFn hash (expand pk signature) = ⟨some witness,true,ec,eh,eb⟩)
    (vr : evalWithAnswerFn hash (verify pk witness) = ⟨some (),true,vc,vh,vb⟩) :
    evalWithAnswerFn hash (pipeline keygen sign expand verify) =
      ⟨true,fun phase => match phase with
        | .keygen => kb | .sign => sb | .expand => eb | .verify => vb,vc⟩ := by
  simp only [pipeline,evalWithAnswerFn_bind,kg,sg,ex,vr,evalWithAnswerFn_pure]
  congr 1
  funext phase
  cases phase <;> rfl

theorem expand_exact (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848) :
    submission.runWith hash .expand (message,pk,wire) =
      ⟨some wire,true,38145,0,0⟩ := by
  have value := Expansion67.run_identity hash (message,pk,wire)
  obtain ⟨finished,_,cycles,calls,blocks⟩ :=
    Expansion67.run_bound hash (message,pk,wire)
  cases h : submission.runWith hash .expand (message,pk,wire)
  simp only [h] at value finished cycles calls blocks
  cases value
  cases finished
  cases cycles
  cases calls
  cases blocks
  rfl

theorem honest_exact (C : Nat) (verifier : HonestVerifier C)
    (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks : Nat, cycles ≤ C ∧
      evalWithAnswerFn hash (submission.honest secretKey message) =
        ⟨true,fun phase => match phase with
          | .keygen => 4255 | .sign => 130710
          | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := publicKey hash secretKey
  let wire := signature hash secretKey message
  obtain ⟨signCycles,_,signRun⟩ :=
    GroupedBalancedSignRunWire67.run_refines hash secretKey
      KeygenFunctional.zeroCache message
  obtain ⟨cycles,calls,blocks,cycleBound,verifyRun⟩ :=
    verifier hash secretKey message
  refine ⟨cycles,calls,blocks,cycleBound,?_⟩
  rw [KeygenOrganizer.honest_eq_pipeline]
  exact pipeline_success hash
    (submission.run .keygen secretKey)
    (fun _ cache => submission.run .sign (secretKey,cache,message))
    (fun p sig => submission.run .expand (message,p,sig))
    (fun p wit => submission.run .verify (message,p,wit))
    pk KeygenFunctional.zeroCache wire wire
    221107 3983 4255 signCycles 122548 130710 38145 0 0
    cycles calls blocks
    (GroupedBalancedKeygenRunFunctional67.run_exact hash secretKey)
    signRun (expand_exact hash message pk wire) verifyRun

theorem completeness (C : Nat) (verifier : HonestVerifier C) :
    submission.Complete := by
  apply KeygenOrganizer.complete_of_honest_success submission
  intro hash secretKey message
  obtain ⟨cycles,calls,blocks,_,run⟩ :=
    honest_exact C verifier hash secretKey message
  rw [run]

theorem compressionBounds (C : Nat) (verifier : HonestVerifier C) :
    submission.CompressionBounds := by
  apply KeygenOrganizer.compressionBounds_of_honest_cost submission
  intro hash secretKey message phase budgeted
  obtain ⟨cycles,calls,blocks,_,run⟩ :=
    honest_exact C verifier hash secretKey message
  rw [run]
  cases phase with
  | keygen => change 4255 ≤ BUDGET_KEYGEN; decide
  | sign => change 130710 ≤ BUDGET_SIGN; decide
  | expand => exact Nat.zero_le _
  | verify => simp [Phase.budgeted] at budgeted

theorem verificationBound (C : Nat) (verifier : HonestVerifier C) :
    submission.VerificationBound C := by
  intro hash secretKey message
  dsimp only
  intro _
  obtain ⟨cycles,calls,blocks,cycleBound,run⟩ :=
    honest_exact C verifier hash secretKey message
  rw [run]
  exact cycleBound

#print axioms expand_exact
#print axioms honest_exact
#print axioms completeness
#print axioms compressionBounds
#print axioms verificationBound

end SigGolfCandidate.Hypertree.GroupedBalancedHonestConditional67
