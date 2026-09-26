import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAudit67
import SigGolfCandidate.Hypertree.SecurityMonitorIndexContact

/-! The audited direct67 H5 state uses the legacy input-labelled provenance
history format, so the strong pair-reuse extractor can consume it directly. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledHistory67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false

def history (audit : Audit) (draws : List Draw) :
    SecurityMonitorIndexState.History :=
  { signedMessages := audit.signedMessages
    indexTrace := draws.map Prod.snd
    nonceGuesses := audit.nonceGuesses }

theorem history_trace (audit : Audit) (draws : List Draw) :
    (history audit draws).indexTrace = draws.map Prod.snd := rfl

theorem history_signed (audit : Audit) (draws : List Draw) :
    (history audit draws).signedMessages = audit.signedMessages := rfl

theorem nonceHit_iff (nonces : Message → Bytes 32)
    (audit : Audit) (draws : List Draw) :
    SecurityMonitorIndexContact.NonceHit nonces (history audit draws) ↔
      ∃ pair ∈ audit.nonceGuesses, nonces pair.1 = pair.2 := by
  constructor
  · rintro ⟨message, member⟩
    exact ⟨(message, nonces message), member, rfl⟩
  · rintro ⟨⟨message, nonce⟩, member, equal⟩
    refine ⟨message, ?_⟩
    change (message, nonces message) ∈ audit.nonceGuesses
    simpa only [equal] using member

theorem provenance_of_audit
    (nonces : Message → Bytes 32)
    (cache : QueryCache HashSpec) (audit : Audit)
    (draws : List Draw)
    (cached : ∀ message nonce answer,
      cache (SecurityRandomOracle.indexInput message nonce) = some answer →
        ∃ marked,
          (SecurityRandomOracle.indexInput message nonce,
            (marked, answer.extractLsb' 0 160)) ∈ draws)
    (signed : ∀ message ∈ audit.signedMessages,
      SecurityMonitorIndexContact.NonceHit nonces (history audit draws) ∨
        ∃ answer,
          cache (SecurityRandomOracle.indexInput message (nonces message)) =
            some answer ∧
          (SecurityRandomOracle.indexInput message (nonces message),
            (true, answer.extractLsb' 0 160)) ∈ draws) :
    SecurityMonitorIndexContact.Provenance nonces cache
      (history audit draws) draws := by
  exact ⟨rfl, cached, signed⟩

#print axioms nonceHit_iff
#print axioms provenance_of_audit

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledHistory67
