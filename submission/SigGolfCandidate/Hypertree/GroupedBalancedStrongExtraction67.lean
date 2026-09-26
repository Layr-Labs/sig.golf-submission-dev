import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
import SigGolfCandidate.Hypertree.GroupedBalancedSignatureReplay67


/-! Deterministic index-reuse extraction for the direct67 grouped scheme.
The nonce/index bookkeeping is independent of the public hypertree geometry,
so it reuses the existing input-labelled H5 provenance monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexReuse67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open SecurityRandomOracle SecurityMonitorIndexState SecurityMonitorIndexContact
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def HonestHistory (hash : Hash) (secretKey : SecretKey)
    (responses : List (Message × GroupedBalancedScheme67.Signature)) : Prop :=
  ∀ entry ∈ responses,
    entry.2.randomizer = Reference.randomizer hash secretKey entry.1

def IndexReuse (hash : Hash)
    (responses : List (Message × GroupedBalancedScheme67.Signature))
    (message : Message) (signature : GroupedBalancedScheme67.Signature) : Prop :=
  ∃ entry ∈ responses, entry.1 ≠ message ∧
    Reference.indexOf hash entry.1 entry.2.randomizer =
      Reference.indexOf hash message signature.randomizer

/-- A reused upper index for a new message is either an H5 trace conflict or
the earlier guess of the honest signer's secret randomizer. The verifier's
own H5 lookup establishes `present`, even when the attacker never queried it. -/
theorem index_reuse_contact (hash : Hash) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (history : History)
    (draws : List SecurityMonitorIndexContact.Draw)
    (tracked : SecurityMonitorIndexContact.Provenance
      (fun m => Reference.randomizer hash secretKey m) cache history draws)
    (agree : cache.AgreesWithFn hash)
    (responses : List (Message × GroupedBalancedScheme67.Signature))
    (honest : HonestHistory hash secretKey responses)
    (signed : ∀ entry ∈ responses, entry.1 ∈ history.signedMessages)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (present : cache (indexInput message signature.randomizer) ≠ none)
    (reuse : IndexReuse hash responses message signature) :
    SecurityIndexTrace.Conflict history.indexTrace ∨
      SecurityMonitorIndexContact.NonceHit
        (fun m => Reference.randomizer hash secretKey m) history := by
  obtain ⟨entry, member, different, same⟩ := reuse
  have nonce := honest entry member
  have distinct :
      indexInput entry.1 (Reference.randomizer hash secretKey entry.1) ≠
        indexInput message signature.randomizer := by
    intro sameInput
    have equalPairs :
        (entry.1, Reference.randomizer hash secretKey entry.1) =
          (message, signature.randomizer) :=
      SecurityForgery.indexInput_pair_injective sameInput
    exact different (congrArg Prod.fst equalPairs)
  have sameIndex :
      (hash (indexInput entry.1 (Reference.randomizer hash secretKey entry.1))).extractLsb' 0 160 =
      (hash (indexInput message signature.randomizer)).extractLsb' 0 160 := by
    simpa only [Reference.indexOf, SecurityRandomOracle.query_eq,
      SecurityRandomOracle.indexInput, nonce] using same
  exact SecurityMonitorIndexContact.index_reuse_contact tracked hash agree
    entry.1 message signature.randomizer (signed entry member) present
    distinct sameIndex

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexReuse67


/-! Deterministic strong-forgery split for the direct67 structured scheme.
At a signed index, freshness forces either a path fault or reuse of the same
160-bit index by a distinct serialized H5 input. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedStrongExtraction67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedMixedPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev History := List (Message × GroupedBalancedScheme67.Signature)

def HonestHistory (hash : Hash) (secretKey : SecretKey)
    (responses : History) : Prop :=
  ∀ entry ∈ responses,
    entry.2 = GroupedBalancedScheme67.sign hash secretKey entry.1

def PairReuse (hash : Hash) (responses : History)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) : Prop :=
  ∃ entry ∈ responses,
    (entry.1, entry.2.randomizer) ≠ (message, signature.randomizer) ∧
    Reference.indexOf hash entry.1 entry.2.randomizer =
      Reference.indexOf hash message signature.randomizer

theorem signed_index_fresh_fault_or_reuse
    (hash : Hash) (secretKey : SecretKey) (responses : History)
    (honest : HonestHistory hash secretKey responses)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (accepted : GroupedBalancedScheme67.verify hash
      (GroupedBalancedScheme67.keygen hash secretKey) message signature)
    (fresh : (message, signature) ∉ responses)
    (signedIndex : ∃ entry ∈ responses,
      Reference.indexOf hash entry.1 entry.2.randomizer =
        Reference.indexOf hash message signature.randomizer) :
    UpperFault hash secretKey
        (Reference.indexOf hash message signature.randomizer) signature ∨
    GroupedBottomExtraction.Bad hash secretKey 10
      (GroupedMixedIndex.bottomTree
        (Reference.indexOf hash message signature.randomizer))
      (Reference.indexOf hash message signature.randomizer).toNat
      signature.bottom ∨
    PairReuse hash responses message signature := by
  obtain ⟨entry, member, sameIndex⟩ := signedIndex
  by_cases pairSame :
      (entry.1, entry.2.randomizer) = (message, signature.randomizer)
  · have messageEq : entry.1 = message := congrArg Prod.fst pairSame
    have randomizerEq : signature.randomizer =
        Reference.randomizer hash secretKey message := by
      have signed := honest entry member
      have nonce := congrArg GroupedBalancedScheme67.Signature.randomizer signed
      change entry.2.randomizer = Reference.randomizer hash secretKey entry.1 at nonce
      exact (congrArg Prod.snd pairSame).symm.trans
        (by simpa only [messageEq] using nonce)
    rcases GroupedBalancedSignatureReplay67.accepted_same_randomizer_exact_or_fault
      hash secretKey message signature randomizerEq accepted with
      upper | bottom | exact
    · exact Or.inl upper
    · exact Or.inr (Or.inl bottom)
    · have sameEntry : entry = (message, signature) := by
        apply Prod.ext messageEq
        exact (honest entry member).trans
          (by simpa only [messageEq] using exact.symm)
      exact False.elim (fresh (sameEntry ▸ member))
  · exact Or.inr (Or.inr ⟨entry, member, pairSame, sameIndex⟩)

#print axioms signed_index_fresh_fault_or_reuse

end SigGolfCandidate.Hypertree.GroupedBalancedStrongExtraction67
