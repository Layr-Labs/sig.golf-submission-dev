import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointIndexBudget67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67

/-! The eager ideal cutoff View fits the physical H-call budget and the
independent lifetime cap for marked H5 index draws. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoffBudget67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphSignBudget67
open GroupedBalancedGraphIndexJointIndexBudget67
open GroupedBalancedGraphIndexJointTotalView67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedIdealEagerCutoff67
open SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem total_mono {α : Type} (view : View α)
    (first second : Nat) (le : first ≤ second)
    (budget : TotalBudget first view) :
    TotalBudget second view := by
  induction view generalizing first second with
  | done value => trivial
  | coin n next ih =>
      exact fun answer => ih answer first second le (budget answer)
  | sign index next ih =>
      exact fun answer => ih answer first second le (budget answer)
  | hash input next ih =>
      change 0 < first ∧ ∀ answer,
        TotalBudget (first - 1) (next answer) at budget
      exact ⟨by omega, fun answer =>
        ih answer (first - 1) (second - 1) (by omega)
          (budget.2 answer)⟩
  | privateHash input outside next ih =>
      change 0 < first ∧ ∀ answer,
        TotalBudget (first - 1) (next answer) at budget
      exact ⟨by omega, fun answer =>
        ih answer (first - 1) (second - 1) (by omega)
          (budget.2 answer)⟩

theorem map_total {α β : Type} (f : α → β)
    (view : View α) (remaining : Nat)
    (budget : TotalBudget remaining view) :
    TotalBudget remaining (mapView f view) := by
  induction view generalizing remaining with
  | done value => trivial
  | coin n next ih => exact fun answer => ih answer remaining (budget answer)
  | sign index next ih => exact fun answer => ih answer remaining (budget answer)
  | hash input next ih =>
      exact ⟨budget.1, fun answer =>
        ih answer (remaining - 1) (budget.2 answer)⟩
  | privateHash input outside next ih =>
      exact ⟨budget.1, fun answer =>
        ih answer (remaining - 1) (budget.2 answer)⟩

theorem eager_cutoff_total {α : Type} (answers : PrivateTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    TotalBudget budget (eagerCutoffView answers cache interaction budget) := by
  induction interaction generalizing budget with
  | done value => trivial
  | coin n next ih => exact fun answer => ih answer budget
  | hash input next ih =>
      cases budget with
      | zero => trivial
      | succ budget =>
          exact ⟨by omega, fun answer =>
            map_total _ _ budget (ih answer budget)⟩
  | sign message next ih =>
      cases budget with
      | zero => trivial
      | succ budget =>
          cases budget with
          | zero => trivial
          | succ budget =>
              change TotalBudget (budget + 1 + 1)
                (mapView _ (.privateHash _ _ (fun indexAnswer =>
                  .sign (indexAnswer.extractLsb' 0 160) (fun bottomAnswer =>
                    mapView _ (eagerCutoffView answers cache
                      (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                        cache (answers (.randomizer message))
                        (indexAnswer.extractLsb' 0 160) bottomAnswer)) budget)))))
              apply map_total
              constructor
              · omega
              · intro indexAnswer
                intro bottomAnswer
                apply map_total
                exact total_mono _ budget (budget + 1) (by omega)
                  (ih _ budget)

theorem map_index {α β : Type} (f : α → β)
    (view : View α) (remaining : Nat)
    (budget : IndexBudget remaining view) :
    IndexBudget remaining (mapView f view) := by
  induction budget with
  | done remaining value => exact .done remaining (f value)
  | hash remaining input next budget ih =>
      exact .hash remaining input _ ih
  | privateOutside remaining input outside parsed next budget ih =>
      exact .privateOutside remaining input outside parsed _ ih
  | privateIndex remaining input outside pair parsed positive next budget ih =>
      exact .privateIndex remaining input outside pair parsed positive _ ih
  | sign remaining index next budget ih =>
      exact .sign remaining index _ ih
  | coin remaining n next budget ih =>
      exact .coin remaining n _ ih

theorem eager_cutoff_index {α : Type} (answers : PrivateTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget remaining : Nat) (signBudget : SignBudget remaining interaction) :
    IndexBudget remaining
      (eagerCutoffView answers cache interaction budget) := by
  induction interaction generalizing budget remaining with
  | done value => exact .done remaining _
  | coin n next ih =>
      exact .coin remaining n _ (fun answer =>
        ih answer budget remaining (signBudget answer))
  | hash input next ih =>
      cases budget with
      | zero => exact .done remaining _
      | succ budget =>
          apply IndexBudget.hash
          intro answer
          exact map_index _ _ remaining
            (ih answer budget remaining (signBudget answer))
  | sign message next ih =>
      cases budget with
      | zero => exact .done remaining _
      | succ budget =>
          cases budget with
          | zero => exact .done remaining _
          | succ budget =>
              change IndexBudget remaining
                (mapView _ (.privateHash _ _ (fun indexAnswer =>
                  .sign (indexAnswer.extractLsb' 0 160) (fun bottomAnswer =>
                    mapView _ (eagerCutoffView answers cache
                      (next (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                        cache (answers (.randomizer message))
                        (indexAnswer.extractLsb' 0 160) bottomAnswer)) budget)))))
              apply map_index
              let randomizer := answers (.randomizer message)
              apply IndexBudget.privateIndex
                (pair := (message, randomizer))
                (parsed := SecurityIndexQuery.parse_index message randomizer)
                (positive := signBudget.1)
              intro indexAnswer
              apply IndexBudget.sign
              intro bottomAnswer
              apply map_index
              exact ih _ budget (remaining - 1) (signBudget.2 _)

#print axioms eager_cutoff_total
#print axioms eager_cutoff_index

end SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoffBudget67
