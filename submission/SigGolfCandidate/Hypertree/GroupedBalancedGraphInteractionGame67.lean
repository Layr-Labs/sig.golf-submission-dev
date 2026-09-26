import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67

/-! An organizer-shaped structured interaction for the direct67 candidate.
Both forgery freshness modes invoke the exact monadic verifier, so verifier
hash queries share the same public monitor as adversary hash queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphInteractionGame67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphInteraction67
set_option maxRecDepth 8192

def ofHash {α β : Type} (program : OracleComp HashSpec α)
    (next : α → Interaction β) : Interaction β :=
  OracleComp.construct next
    (fun query _ continuation => .hash query continuation) program

@[simp] theorem ofHash_pure {α β : Type} (value : α)
    (next : α → Interaction β) :
    ofHash (pure value) next = next value := rfl

theorem ofHash_query {α β : Type} (query : Query)
    (resume : BitVec 256 → OracleComp HashSpec α)
    (next : α → Interaction β) :
    ofHash (liftM (HashSpec.query query) >>= resume) next =
      .hash query (fun answer => ofHash (resume answer) next) := rfl

inductive Forgery where
  | witness (message : Message) (signature : GroupedBalancedScheme67.Signature)
  | signature (message : Message) (signature : GroupedBalancedScheme67.Signature)

structure Transcript where
  signed : List (Message × List Byte) := []
  signingRequests : Nat := 0

def Transcript.freshMessage (transcript : Transcript) (message : Message) : Bool :=
  !transcript.signed.any (fun entry => entry.1 == message)

def Transcript.freshSignature (transcript : Transcript)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) : Bool :=
  !transcript.signed.contains (message, signature.encode)

structure Result where
  won : Bool
  candidate : Option (Message × GroupedBalancedScheme67.Signature)
  transcript : Transcript

def ofCheck (pk : PublicKey) (transcript : Transcript) :
    Forgery → Interaction Result
  | .witness message signature =>
      ofHash (GroupedBalancedVerifyOracle67.verify pk message signature)
        (fun accepted => .done
          ⟨accepted && transcript.freshMessage message,
            some (message, signature), transcript⟩)
  | .signature message signature =>
      ofHash (GroupedBalancedVerifyOracle67.verify pk message signature)
        (fun accepted => .done
          ⟨accepted && transcript.freshSignature message signature,
            some (message, signature), transcript⟩)

inductive Action (state : Type) where
  | submit (forgery : Forgery)
  | hash (input : Query) (resume : BitVec 256 → state)
  | sign (message : Message)
      (resume : GroupedBalancedScheme67.Signature → state)
  | sample (n : Nat) (resume : Fin (n + 1) → state)
  | step (next : state)

structure Adversary where
  State : Type
  initial : PublicKey → State
  step : State → Action State

def ofInteract (adversary : Adversary) (pk : PublicKey) :
    Nat → adversary.State → Transcript → Interaction Result
  | 0, _, transcript => .done ⟨false, none, transcript⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit forgery => ofCheck pk transcript forgery
      | .hash input resume => .hash input (fun answer =>
          ofInteract adversary pk rounds (resume answer) transcript)
      | .sign message resume =>
          if transcript.signingRequests < LIFETIME then
            .sign message (fun signature =>
              let next : Transcript :=
                { transcript with
                  signed := (message, signature.encode) :: transcript.signed
                  signingRequests := transcript.signingRequests + 1 }
              ofInteract adversary pk rounds (resume signature) next)
          else .done ⟨false, none, transcript⟩
      | .sample n resume => .coin n (fun answer =>
          ofInteract adversary pk rounds (resume answer) transcript)
      | .step next => ofInteract adversary pk rounds next transcript

theorem interaction_contact_le (secretKey : SecretKey)
    (adversary : Adversary) (rounds remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
      GroupedBalancedGraphMonitorSignCoupling67.execute table
        (GroupedBalancedGraphInteraction67.toView secretKey
          (GroupedBalancedGraphMonitorSetup67.cache table)
          (ofInteract adversary
            (GroupedBalancedGraphMonitorSetupBound67.rootFrom
              (GroupedBalancedGraphMonitorSetup67.cache table))
            rounds
            (adversary.initial
              (GroupedBalancedGraphMonitorSetupBound67.rootFrom
                (GroupedBalancedGraphMonitorSetup67.cache table)))
            {}))
        remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  apply GroupedBalancedGraphInteraction67.interaction_contact_le secretKey
    (fun cache => ofInteract adversary
      (GroupedBalancedGraphMonitorSetupBound67.rootFrom cache)
      rounds (adversary.initial
        (GroupedBalancedGraphMonitorSetupBound67.rootFrom cache)) {}) remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphInteractionGame67
