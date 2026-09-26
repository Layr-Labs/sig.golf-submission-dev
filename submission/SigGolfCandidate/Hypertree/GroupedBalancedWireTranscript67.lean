import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67

/-! A byte-exact bridge from the organizer's two forgery forms to direct67
structured signatures and its signed-response history. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedWireTranscript67
open SigGolf Reference GroupedBalancedWire67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev sizes : Sizes := GroupedBalancedProgram67.sizes
abbrev History := List (Message × GroupedBalancedScheme67.Signature)

def responses (transcript : Transcript sizes) : History :=
  transcript.signed.map (fun entry => (entry.1, decode entry.2))

theorem decode_injective : Function.Injective decode := by
  intro first second same
  calc
    first = wire (decode first) := (decode_wire first).symm
    _ = wire (decode second) := congrArg wire same
    _ = second := decode_wire second

@[simp] theorem mem_responses (transcript : Transcript sizes)
    (message : Message) (value : Bytes 50848) :
    (message, decode value) ∈ responses transcript ↔
      (message, value) ∈ transcript.signed := by
  rw [responses, List.mem_map]
  constructor
  · rintro ⟨⟨other, encoded⟩, member, same⟩
    have messageSame : other = message := congrArg Prod.fst same
    have wireSame : encoded = value := decode_injective (congrArg Prod.snd same)
    simpa only [messageSame, wireSame] using member
  · intro member
    exact ⟨(message, value), member, rfl⟩

theorem fresh_message (transcript : Transcript sizes) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (fresh : transcript.freshMessage message = true) :
    (message, signature) ∉ responses transcript := by
  intro present
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  have messageSame : entry.1 = message := congrArg Prod.fst same
  have all := (List.any_eq_false).mp
    (show transcript.signed.any (fun entry => entry.1 == message) = false from
      by simpa only [Transcript.freshMessage, Bool.not_eq_true'] using fresh)
  have absent := all entry member
  simp only [messageSame, beq_self_eq_true, not_true_eq_false] at absent

theorem fresh_signature (transcript : Transcript sizes) (message : Message)
    (value : Bytes 50848)
    (fresh : transcript.freshSignature message value = true) :
    (message, decode value) ∉ responses transcript := by
  rw [mem_responses]
  intro present
  have contained : transcript.signed.contains (message, value) = true :=
    List.contains_iff_mem.mpr present
  change (!transcript.signed.contains (message, value)) = true at fresh
  rw [contained] at fresh
  cases fresh

def candidate : Forgery sizes → Message × GroupedBalancedScheme67.Signature
  | .witness message witness => (message, decode witness)
  | .signature message value => (message, decode value)

def fresh (transcript : Transcript sizes) : Forgery sizes → Bool
  | .witness message _ => transcript.freshMessage message
  | .signature message value => transcript.freshSignature message value

theorem fresh_candidate (transcript : Transcript sizes)
    (forgery : Forgery sizes) (accepted : fresh transcript forgery = true) :
    candidate forgery ∉ responses transcript := by
  cases forgery with
  | witness message witness => exact fresh_message transcript message _ accepted
  | signature message value => exact fresh_signature transcript message value accepted

def afterSign (transcript : Transcript sizes) (message : Message)
    (response : Option (Bytes 50848)) : Transcript sizes :=
  { transcript with
    signed := match response with
      | none => transcript.signed
      | some value => (message, value) :: transcript.signed
    signingRequests := transcript.signingRequests + 1 }

@[simp] theorem responses_after_signature (transcript : Transcript sizes)
    (message : Message) (value : Bytes 50848) :
    responses (afterSign transcript message (some value)) =
      (message, decode value) :: responses transcript := rfl

@[simp] theorem responses_after_structured (transcript : Transcript sizes)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) :
    responses (afterSign transcript message (some (wire signature))) =
      (message, signature) :: responses transcript := by
  rw [responses_after_signature, wire_decode]

#print axioms fresh_candidate
#print axioms responses_after_structured

end SigGolfCandidate.Hypertree.GroupedBalancedWireTranscript67
