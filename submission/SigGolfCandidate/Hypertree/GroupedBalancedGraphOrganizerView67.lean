import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteractionGame67

/-! The organizer's arbitrary wire-based adversary and both forgery variants
embed into the direct67 monitor. Encoder and decoders are explicit parameters;
the bytecode refinement certificate will identify them with the four images. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphInteractionGame67
set_option maxRecDepth 8192

structure Result (sizes : Sizes) where
  won : Bool
  candidate : Option (Message × GroupedBalancedScheme67.Signature)
  transcript : SigGolf.Transcript sizes

def ofCheck (sizes : Sizes)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (pk : PublicKey) (transcript : SigGolf.Transcript sizes) :
    SigGolf.Forgery sizes → Interaction (Result sizes)
  | .witness message witness =>
      let signature := decodeWitness witness
      ofHash (GroupedBalancedVerifyOracle67.verify pk message signature)
        (fun accepted => .done
          ⟨accepted && transcript.freshMessage message,
            some (message, signature), transcript⟩)
  | .signature message wire =>
      let signature := decodeSignature wire
      ofHash (GroupedBalancedVerifyOracle67.verify pk message signature)
        (fun accepted => .done
          ⟨accepted && transcript.freshSignature message wire,
            some (message, signature), transcript⟩)

def ofInteract (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes) (pk : PublicKey) :
    Nat → adversary.State → SigGolf.Transcript sizes →
      Interaction (Result sizes)
  | 0, _, transcript => .done ⟨false, none, transcript⟩
  | rounds + 1, state, transcript =>
      match adversary.step state with
      | .submit forgery =>
          ofCheck sizes decodeWitness decodeSignature pk transcript forgery
      | .hash input resume => .hash input (fun answer =>
          ofInteract sizes encode decodeWitness decodeSignature adversary pk
            rounds (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 })
      | .sign request resume =>
          if transcript.signingRequests < LIFETIME then
            .sign request.message (fun signature =>
              let wire := encode signature
              let next : SigGolf.Transcript sizes :=
                { transcript with
                  signed := (request.message, wire) :: transcript.signed
                  signingRequests := transcript.signingRequests + 1 }
              ofInteract sizes encode decodeWitness decodeSignature adversary pk
                rounds (resume (some wire)) next)
          else .done ⟨false, none, transcript⟩
      | .sample n resume => .coin n (fun answer =>
          ofInteract sizes encode decodeWitness decodeSignature adversary pk
            rounds (resume answer) transcript)
      | .step next =>
          ofInteract sizes encode decodeWitness decodeSignature adversary pk
            rounds next transcript

theorem organizer_contact_le (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds remaining : Nat) :
    Pr[= none | do
      let table ← $ᵗ GroupedBalancedGraphPassive67.PointTable
      let exposed := GroupedBalancedGraphMonitorSetup67.cache table
      let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
      GroupedBalancedGraphMonitorSignCoupling67.execute table
        (GroupedBalancedGraphInteraction67.toView secretKey exposed
          (ofInteract sizes encode decodeWitness decodeSignature adversary pk
            rounds (adversary.initial pk publicCache) {}))
        remaining
        (GroupedBalancedGraphMonitorSignBound67.initial exposed)] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  apply GroupedBalancedGraphInteraction67.interaction_contact_le secretKey
    (fun exposed =>
      let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
      ofInteract sizes encode decodeWitness decodeSignature adversary pk
        rounds (adversary.initial pk publicCache) {}) remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67
