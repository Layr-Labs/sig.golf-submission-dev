import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointViewBudget67

/-! Only the tag-5 private index read can mark an H5 draw. The tag-6
randomizer read is outside the parsed H5 domain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexBudget67
open SigGolf OracleSpec Reference
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphSignBudget67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

inductive IndexBudget {α : Type} : Nat → View α → Prop where
  | done (remaining : Nat) (value : α) : IndexBudget remaining (.done value)
  | hash (remaining : Nat) (input : Query)
      (next : BitVec 256 → View α)
      (budget : ∀ answer, IndexBudget remaining (next answer)) :
      IndexBudget remaining (.hash input next)
  | privateOutside (remaining : Nat) (input : Query)
      (outside : GroupedBalancedGraphQuery67.locate input = none)
      (parsed : SecurityIndexQuery.parse input = none)
      (next : BitVec 256 → View α)
      (budget : ∀ answer, IndexBudget remaining (next answer)) :
      IndexBudget remaining (.privateHash input outside next)
  | privateIndex (remaining : Nat) (input : Query)
      (outside : GroupedBalancedGraphQuery67.locate input = none)
      (pair : Message × Bytes 32)
      (parsed : SecurityIndexQuery.parse input = some pair)
      (positive : 0 < remaining)
      (next : BitVec 256 → View α)
      (budget : ∀ answer, IndexBudget (remaining - 1) (next answer)) :
      IndexBudget remaining (.privateHash input outside next)
  | sign (remaining : Nat) (index : BitVec 160)
      (next : BitVec 256 → View α)
      (budget : ∀ answer, IndexBudget remaining (next answer)) :
      IndexBudget remaining (.sign index next)
  | coin (remaining n : Nat)
      (next : Fin (n + 1) → View α)
      (budget : ∀ answer, IndexBudget remaining (next answer)) :
      IndexBudget remaining (.coin n next)

theorem parse_randomizer_none (secretKey : SecretKey) (message : Message) :
    SecurityIndexQuery.parse
      (SecurityRandomOracle.randomizerInput secretKey message) = none := by
  apply (SecurityIndexQuery.parse_none_iff _).2
  intro other randomizer same
  exact SecurityRandomOracle.indexInput_ne_randomizerInput
    other message randomizer secretKey same

theorem honest_sign_budget {α : Type} (secretKey : SecretKey)
    (message : Message)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (next : GroupedBalancedScheme67.Signature → View α) (remaining : Nat)
    (budget : ∀ signature, IndexBudget remaining (next signature)) :
    IndexBudget (remaining + 1)
      (honestSign secretKey message cache next) := by
  unfold honestSign
  apply IndexBudget.privateOutside
    (parsed := parse_randomizer_none secretKey message)
  intro randomizer
  apply IndexBudget.privateIndex
    (pair := (message, randomizer))
    (parsed := SecurityIndexQuery.parse_index message randomizer)
    (positive := by omega)
  intro indexAnswer
  apply IndexBudget.sign
  intro bottomAnswer
  simpa only [Nat.add_sub_cancel_right] using
    budget (signatureFromAnswers cache randomizer
      (indexAnswer.extractLsb' 0 160) bottomAnswer)

theorem to_view_budget {α : Type} (secretKey : SecretKey)
    (cache : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (interaction : Interaction α) (remaining : Nat)
    (budget : SignBudget remaining interaction) :
    IndexBudget remaining (toView secretKey cache interaction) := by
  induction interaction generalizing remaining with
  | done value => exact .done remaining value
  | hash input next ih =>
      change ∀ answer, SignBudget remaining (next answer) at budget
      exact .hash remaining input _ (fun answer =>
        ih answer remaining (budget answer))
  | coin n next ih =>
      change ∀ answer, SignBudget remaining (next answer) at budget
      exact .coin remaining n _ (fun answer =>
        ih answer remaining (budget answer))
  | sign message next ih =>
      change 0 < remaining ∧ ∀ signature,
        SignBudget (remaining - 1) (next signature) at budget
      have remainingEq : remaining = (remaining - 1) + 1 := by omega
      rw [remainingEq]
      exact honest_sign_budget secretKey message cache (fun signature =>
        toView secretKey cache (next signature)) (remaining - 1)
        (fun signature => ih signature (remaining - 1) (budget.2 signature))

#print axioms to_view_budget

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexBudget67
