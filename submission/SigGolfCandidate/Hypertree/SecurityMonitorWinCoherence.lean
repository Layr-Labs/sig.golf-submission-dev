import SigGolfCandidate.Hypertree.SecurityMonitorView
import SigGolfCandidate.Hypertree.SecurityMonitorIndexContactView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorCompose

/-! Inlined from SigGolfCandidate.Hypertree.SecurityMonitorTranscript; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorWinCoherence. -/
section
namespace SigGolfCandidate.Hypertree.SecurityMonitorTranscript
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityExperiment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Decode exactly the organizer's successful signing responses. -/
def responses (transcript : Transcript submission.sizes) : SecurityForgery.History :=
  transcript.signed.map (fun entry => (entry.1, decode entry.2))

theorem decode_injective : Function.Injective decode := by
  intro first second same
  apply SecurityPacking.bytes_injective signatureBytes
  calc
    bytes first = (decode first).encode := (decode_encode first).symm
    _ = (decode second).encode := congrArg Compact.encode same
    _ = bytes second := decode_encode second

@[simp] theorem mem_responses (transcript : Transcript submission.sizes) (message : Message) (wire : Bytes signatureBytes) :
    (message, decode wire) ∈ responses transcript ↔ (message,wire) ∈ transcript.signed := by
  rw [responses, List.mem_map]
  constructor
  · rintro ⟨⟨other,encoded⟩, member, same⟩
    have messageSame : other = message := congrArg Prod.fst same
    have wireSame : encoded = wire := decode_injective (congrArg Prod.snd same)
    simpa only [messageSame, wireSame] using member
  · intro member
    exact ⟨(message,wire),member,rfl⟩

theorem fresh_message (transcript : Transcript submission.sizes) (message : Message) (signature : Compact)
    (fresh : transcript.freshMessage message = true) : (message,signature) ∉ responses transcript := by
  intro present
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  have messageSame : entry.1 = message := congrArg Prod.fst same
  have all := (List.any_eq_false).mp (show transcript.signed.any (fun entry => entry.1 == message) = false from
    by simpa only [Transcript.freshMessage, Bool.not_eq_true'] using fresh)
  have absent := all entry member
  simp only [messageSame, beq_self_eq_true, not_true_eq_false] at absent

theorem fresh_signature (transcript : Transcript submission.sizes) (message : Message) (wire : Bytes signatureBytes)
    (fresh : transcript.freshSignature message wire = true) : (message,decode wire) ∉ responses transcript := by
  rw [mem_responses]
  intro present
  have contained : transcript.signed.contains (message,wire) = true := List.contains_iff_mem.mpr present
  change (!transcript.signed.contains (message,wire)) = true at fresh
  rw [contained] at fresh
  cases fresh

@[simp] theorem responses_after_signature (transcript : Transcript submission.sizes) (message : Message)
    (wire : Bytes signatureBytes) :
    responses (SecurityExperimentAtomic.afterSign transcript message (some wire)) = (message,decode wire)::responses transcript := rfl

@[simp] theorem responses_after_valid (transcript : Transcript submission.sizes) (message : Message)
    (signature : Compact) (valid : signature.Valid) :
    responses (SecurityExperimentAtomic.afterSign transcript message (serialize signature)) = (message,signature)::responses transcript := by
  rw [serialize_valid signature valid, responses_after_signature, wire_decode]

/-- Both organizer submission forms exclude replay in the decoded response history. -/
def candidate : Forgery submission.sizes → Message × Compact
  | .witness message witness => (message,decode witness)
  | .signature message wire => (message,decode wire)

def fresh (transcript : Transcript submission.sizes) : Forgery submission.sizes → Bool
  | .witness message _ => transcript.freshMessage message
  | .signature message wire => transcript.freshSignature message wire

theorem fresh_candidate (transcript : Transcript submission.sizes) (forgery : Forgery submission.sizes)
    (accepted : fresh transcript forgery = true) : candidate forgery ∉ responses transcript := by
  cases forgery with
  | witness message witness => exact fresh_message transcript message _ accepted
  | signature message wire => exact fresh_signature transcript message wire accepted

/-- This is the actual final checker, with one common continuation for either mode. -/
theorem ofCheck_eq (pk : PublicKey) (transcript : Transcript submission.sizes) (forgery : Forgery submission.sizes) :
    SecurityMonitorView.ofCheck pk transcript forgery =
      SecurityMonitorView.ofHash (SecurityVerify.verifyCompact pk (candidate forgery).1 (candidate forgery).2)
        (fun accepted => .done ⟨accepted && fresh transcript forgery, some (candidate forgery), transcript⟩) := by
  cases forgery <;> rfl

#print axioms fresh_candidate
end SigGolfCandidate.Hypertree.SecurityMonitorTranscript

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorWin
open SigGolf OracleComp OracleSpec Reference SignatureEncoding SecurityGraphFactor
  SecurityGraphReference SecurityGraphSigner SecurityGraphExtraction SecurityGraphMonitorCompose
  SecurityMonitorIndexState SecurityMonitorTranscript SecurityMonitorIndexContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- The recorded transcript is honest for every total oracle extending the
actual residual cache, and its indices are exactly the authorization history. -/
def Coherent (factors : Factors) (cache : QueryCache HashSpec) (history : History)
    (transcript : Transcript submission.sizes) : Prop :=
  (∀ entry ∈ responses transcript, entry.1 ∈ history.signedMessages) ∧
    ∀ base : Hash, cache.AgreesWithFn base →
      HonestHistory factors base (responses transcript) ∧
      history.signedIndices = Signed factors base (responses transcript)

theorem coherent_empty (factors : Factors) : Coherent factors ∅ (recordKeygen {}) {} := by
  constructor
  · intro entry member; cases member
  · intro base agree
    constructor
    · intro entry member; cases member
    · rfl

theorem Coherent.public {factors : Factors} {cache : QueryCache HashSpec} {history : History}
    {transcript : Transcript submission.sizes} (coherent : Coherent factors cache history transcript)
    (query : Query) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((SecurityGraphOracle.publicOracle
      (privateTable factors) (labels factors) query).run cache)) :
    Coherent factors residual (recordPublic history query (cache query).isSome answer) transcript := by
  constructor
  · intro entry present
    rw [public_messages]
    exact coherent.1 entry present
  · intro base agree
    have old := coherent.2 base (query_support_agrees factors query cache (answer,residual) member base agree).1
    exact ⟨old.1, (SecurityMonitorGraphState.public_indices _ _ _ _).trans old.2⟩

 theorem random_support_agrees (query : Query) (cache : QueryCache HashSpec)
    (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((randomOracle (spec := HashSpec) query).run cache))
    (base : Hash) (agree : residual.AgreesWithFn base) :
    cache.AgreesWithFn base ∧ base query = answer := by
  cases present : cache query with
  | some value =>
    simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩
    exact ⟨agree, agree present⟩
  | none =>
    simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨value, _, equal⟩ := member
    cases equal
    exact (QueryCache.agreesWithFn_cacheQuery_iff cache query answer base present).mp agree

 theorem upperLayers_length (privateAnswers : SecurityGraphIdeal.PrivateTable) (labels : SecurityGraph.Labels)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    (upperLayers privateAnswers labels count level index hl hi message).length = count := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih => simp only [upperLayers, List.length_cons, ih]

 theorem signature_valid (privateAnswers : SecurityGraphIdeal.PrivateTable) (labels : SecurityGraph.Labels)
    (nonce : Bytes 32) (index : BitVec 160) : (signature privateAnswers labels nonce index).Valid :=
  by
    apply upperLayers_length

 theorem Coherent.sign {factors : Factors} {cache : QueryCache HashSpec} {history : History}
    {transcript : Transcript submission.sizes} (coherent : Coherent factors cache history transcript)
    (message : Message) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((randomOracle (spec := HashSpec)
      (SecurityRandomOracle.indexInput message (factors.2.1 message))).run cache)) :
    Coherent factors residual
      (recordSign history message (cache (SecurityRandomOracle.indexInput message (factors.2.1 message))).isSome answer)
      (SecurityExperimentAtomic.afterSign transcript message (SecurityExperiment.serialize
        (signature (privateTable factors) (labels factors) (factors.2.1 message) (answer.extractLsb' 0 160)))) := by
  rw [Coherent, responses_after_valid _ _ _ (signature_valid _ _ _ _)]
  constructor
  · intro entry present
    rcases List.mem_cons.mp present with same | old
    · subst entry; exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (coherent.1 entry old)
  · intro base agree
    have replay := random_support_agrees _ cache answer residual member base agree
    have old := coherent.2 base replay.1
    have nonce : privateTable factors (.randomizer message) = factors.2.1 message := rfl
    have indexEq : indexOf (programmed (privateTable factors) (labels factors) base) message (factors.2.1 message) = answer.extractLsb' 0 160 := by
      rw [index_residual, replay.2]
    constructor
    · intro entry present
      rcases List.mem_cons.mp present with same | present
      · subst entry
        simp only [nonce, indexEq]
      · exact old.1 entry present
    · change insert (answer.extractLsb' 0 160) history.signedIndices = _
      rw [old.2]
      simp only [Signed, List.map_cons, List.toFinset_cons]
      congr 1
      change answer.extractLsb' 0 160 = indexOf _ message (factors.2.1 message)
      exact indexEq.symm

end SigGolfCandidate.Hypertree.SecurityMonitorWin
