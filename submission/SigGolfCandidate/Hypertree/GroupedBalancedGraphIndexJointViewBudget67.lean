import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrganizerView67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJoint67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphSignBudget67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67. -/
section
/-! A syntax-level lifetime bound for organizer interactions. A sign action
consumes one signing slot; public hashes and verifier hashes consume none. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSignBudget67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphInteractionGame67
open GroupedBalancedGraphOrganizerView67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def SignBudget {α : Type} : Nat → Interaction α → Prop
  | _, .done _ => True
  | remaining, .hash _ next =>
      ∀ answer, SignBudget remaining (next answer)
  | remaining, .sign _ next =>
      0 < remaining ∧
        ∀ signature, SignBudget (remaining - 1) (next signature)
  | remaining, .coin _ next =>
      ∀ answer, SignBudget remaining (next answer)

theorem ofHash_budget {α β : Type}
    (program : OracleComp HashSpec α)
    (next : α → Interaction β) (remaining : Nat)
    (budget : ∀ value, SignBudget remaining (next value)) :
    SignBudget remaining (ofHash program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact budget value
  | query_bind input resume ih =>
      rw [ofHash_query]
      exact fun answer => ih answer

theorem check_budget (sizes : Sizes)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (pk : PublicKey) (transcript : SigGolf.Transcript sizes)
    (forgery : SigGolf.Forgery sizes) (remaining : Nat) :
    SignBudget remaining
      (GroupedBalancedGraphOrganizerView67.ofCheck sizes
        decodeWitness decodeSignature pk transcript forgery) := by
  cases forgery with
  | witness message witness =>
      exact ofHash_budget _ _ remaining (fun _ => trivial)
  | signature message wire =>
      exact ofHash_budget _ _ remaining (fun _ => trivial)

theorem interact_budget (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (adversary : SigGolf.Adversary sizes) (pk : PublicKey)
    (rounds : Nat) (state : adversary.State)
    (transcript : SigGolf.Transcript sizes) :
    SignBudget (LIFETIME - transcript.signingRequests)
      (GroupedBalancedGraphOrganizerView67.ofInteract sizes
        encode decodeWitness decodeSignature adversary pk
        rounds state transcript) := by
  induction rounds generalizing state transcript with
  | zero => trivial
  | succ rounds ih =>
      cases action : adversary.step state with
      | submit forgery =>
          simpa only [GroupedBalancedGraphOrganizerView67.ofInteract, action]
            using check_budget sizes decodeWitness decodeSignature pk transcript
              forgery (LIFETIME - transcript.signingRequests)
      | hash input resume =>
          simp only [GroupedBalancedGraphOrganizerView67.ofInteract,
            action, SignBudget]
          intro answer
          exact ih (resume answer)
            { transcript with hashCalls := transcript.hashCalls + 1 }
      | sign message resume =>
          by_cases allowed : transcript.signingRequests < LIFETIME
          · simp only [GroupedBalancedGraphOrganizerView67.ofInteract,
              action, if_pos allowed, SignBudget]
            constructor
            · omega
            · intro signature
              let nextTranscript : SigGolf.Transcript sizes :=
                { transcript with
                  signed := (message.message, encode signature) ::
                    transcript.signed
                  signingRequests := transcript.signingRequests + 1 }
              have nextBudget :=
                ih (resume (some (encode signature))) nextTranscript
              have remainingEq :
                  LIFETIME - nextTranscript.signingRequests =
                    (LIFETIME - transcript.signingRequests) - 1 := by
                simp only [nextTranscript]
                omega
              simpa only [remainingEq] using nextBudget
          · simp only [GroupedBalancedGraphOrganizerView67.ofInteract,
              action, if_neg allowed, SignBudget]
      | sample n resume =>
          simp only [GroupedBalancedGraphOrganizerView67.ofInteract,
            action, SignBudget]
          exact fun answer => ih (resume answer) transcript
      | step next =>
          simpa only [GroupedBalancedGraphOrganizerView67.ofInteract,
            action] using ih next transcript

#print axioms interact_budget

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSignBudget67

end

/-! Count every private signing hash step, including the randomizer step.
This gives a two-per-signing lifetime cap independent of query parsing. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphSignBudget67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def PrivateBudget {α : Type} : Nat → View α → Prop
  | _, .done _ => True
  | remaining, .hash _ next =>
      ∀ answer, PrivateBudget remaining (next answer)
  | remaining, .privateHash _ _ next =>
      0 < remaining ∧ ∀ answer,
        PrivateBudget (remaining - 1) (next answer)
  | remaining, .sign _ next =>
      ∀ answer, PrivateBudget remaining (next answer)
  | remaining, .coin _ next =>
      ∀ answer, PrivateBudget remaining (next answer)

theorem honest_sign_budget {α : Type} (secretKey : SecretKey)
    (message : Message) (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (next : GroupedBalancedScheme67.Signature → View α) (remaining : Nat)
    (budget : ∀ signature, PrivateBudget remaining (next signature)) :
    PrivateBudget (remaining + 2)
      (honestSign secretKey message cache next) := by
  change 0 < remaining + 2 ∧ ∀ randomizer : BitVec 256,
    PrivateBudget ((remaining + 2) - 1)
      (.privateHash (SecurityRandomOracle.indexInput message randomizer)
        (locate_index_none message randomizer) (fun indexAnswer =>
          let index : BitVec 160 := indexAnswer.extractLsb' 0 160
          .sign index (fun bottomAnswer =>
            next (signatureFromAnswers cache randomizer index bottomAnswer))))
  constructor
  · omega
  · intro randomizer
    change 0 < (remaining + 2) - 1 ∧ ∀ indexAnswer : BitVec 256,
      PrivateBudget (((remaining + 2) - 1) - 1)
        (.sign (indexAnswer.extractLsb' 0 160) (fun bottomAnswer =>
          next (signatureFromAnswers cache randomizer
            (indexAnswer.extractLsb' 0 160) bottomAnswer)))
    constructor
    · omega
    · intro indexAnswer
      change ∀ bottomAnswer : BitVec 256,
        PrivateBudget (((remaining + 2) - 1) - 1)
          (next (signatureFromAnswers cache randomizer
            (indexAnswer.extractLsb' 0 160) bottomAnswer))
      have remainingEq : ((remaining + 2) - 1) - 1 = remaining := by omega
      rw [remainingEq]
      exact fun bottomAnswer => budget
        (signatureFromAnswers cache randomizer
          (indexAnswer.extractLsb' 0 160) bottomAnswer)

theorem to_view_budget {α : Type} (secretKey : SecretKey)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (interaction : Interaction α) (remaining : Nat)
    (budget : SignBudget remaining interaction) :
    PrivateBudget (2 * remaining) (toView secretKey cache interaction) := by
  induction interaction generalizing remaining with
  | done value => trivial
  | hash input next ih =>
      change ∀ answer, SignBudget remaining (next answer) at budget
      exact fun answer => ih answer remaining (budget answer)
  | coin n next ih =>
      change ∀ answer, SignBudget remaining (next answer) at budget
      exact fun answer => ih answer remaining (budget answer)
  | sign message next ih =>
      change 0 < remaining ∧ ∀ signature,
        SignBudget (remaining - 1) (next signature) at budget
      have eqRemaining : 2 * remaining = 2 * (remaining - 1) + 2 := by omega
      rw [eqRemaining]
      exact honest_sign_budget secretKey message cache
        (fun signature => toView secretKey cache (next signature))
        (2 * (remaining - 1))
        (fun signature => ih signature (remaining - 1) (budget.2 signature))

#print axioms to_view_budget

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67
