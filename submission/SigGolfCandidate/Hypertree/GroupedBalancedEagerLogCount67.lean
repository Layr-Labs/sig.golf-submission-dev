import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67

/-! The secret-key-class counter in the joint monitor is the secret-key
component of the eager ideal action log on every completed path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEagerLogCount67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphIndexJointClassTrace67
open SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private theorem mapView_comp {α β γ : Type} (f : β → γ) (g : α → β)
    (view : View α) :
    mapView f (mapView g view) = mapView (fun value => f (g value)) view := by
  induction view with
  | done value => rfl
  | coin n next ih =>
      simp only [mapView]
      exact congrArg (View.coin n) (funext (fun answer => ih answer))
  | sign index next ih =>
      simp only [mapView]
      exact congrArg (View.sign index) (funext (fun answer => ih answer))
  | hash input next ih =>
      simp only [mapView]
      exact congrArg (View.hash input) (funext (fun answer => ih answer))
  | privateHash input outside next ih =>
      simp only [mapView]
      exact congrArg (View.privateHash input outside)
        (funext (fun answer => ih answer))

private theorem annotate_mapView {α β : Type} (f : α → β)
    (view : View α) (secret : Nat) :
    annotate (mapView f view) secret =
      mapView (fun result : α × Nat => (f result.1, result.2))
        (annotate view secret) := by
  induction view generalizing secret with
  | done value => rfl
  | coin n next ih =>
      simp only [mapView, annotate]
      exact congrArg (View.coin n) (funext (fun answer => ih answer secret))
  | sign index next ih =>
      simp only [mapView, annotate]
      exact congrArg (View.sign index) (funext (fun answer => ih answer secret))
  | hash input next ih =>
      simp only [mapView, annotate]
      exact congrArg (View.hash input)
        (funext (fun answer => ih answer (secret + secretCharge input)))
  | privateHash input outside next ih =>
      simp only [mapView, annotate]
      exact congrArg (View.privateHash input outside)
        (funext (fun answer => ih answer secret))

noncomputable def marked {α : Type} (secret : Nat)
    (result : α × List Action) : (α × List Action) × Nat :=
  (result, secret + (counts result.2).secretKey)

private theorem charge_secret (action : Action) :
    action.charge.secretKey =
      match action with
      | .publicHash input => secretCharge input
      | .privateHash => 0 := by
  cases action with
  | publicHash input => rfl
  | privateHash => rfl

private theorem prepend_marked {α : Type} (action : Action)
    (view : View (α × List Action)) (secret : Nat)
    (hyp : annotate view (secret + action.charge.secretKey) =
      mapView (marked (secret + action.charge.secretKey)) view) :
    annotate (prependAction action view)
        (secret + action.charge.secretKey) =
      mapView (marked secret) (prependAction action view) := by
  unfold prependAction
  rw [annotate_mapView, hyp, mapView_comp, mapView_comp]
  congr 1
  funext result
  cases result with
  | mk value trace =>
      simp only [marked, counts]
      congr 1
      omega

theorem eager_log_count {α : Type} (answers : PrivateTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget secret : Nat) :
    annotate (eagerCutoffView answers cache interaction budget) secret =
      mapView (marked secret)
        (eagerCutoffView answers cache interaction budget) := by
  induction interaction generalizing budget secret with
  | done value =>
      simp [eagerCutoffView, annotate, mapView, marked, counts]
  | coin n next ih =>
      simp only [eagerCutoffView, annotate, mapView]
      exact congrArg (View.coin n)
        (funext (fun answer => ih answer budget secret))
  | hash input next ih =>
      cases budget with
      | zero =>
          simp [eagerCutoffView, annotate, mapView, marked, counts]
      | succ budget =>
          change View.hash input
              (fun answer => annotate
                (prependAction (.publicHash input)
                  (eagerCutoffView answers cache (next answer) budget))
                (secret + secretCharge input)) =
            View.hash input
              (fun answer => mapView (marked secret)
                (prependAction (.publicHash input)
                  (eagerCutoffView answers cache (next answer) budget)))
          apply congrArg (View.hash input)
          funext answer
          apply prepend_marked
          simpa only [Action.charge, GroupedBalancedQueryClasses67.charge,
            secretCharge] using ih answer budget
            (secret + secretCharge input)
  | sign message next ih =>
      cases budget with
      | zero =>
          simp [eagerCutoffView, annotate, mapView, marked, counts]
      | succ budget =>
          cases budget with
          | zero =>
              simp [eagerCutoffView, prependAction, mapView, annotate,
                marked, counts, Action.charge]
          | succ budget =>
              let randomizer := answers (.randomizer message)
              let input := SecurityRandomOracle.indexInput message randomizer
              let body : View (Option α × List Action) :=
                .privateHash input (locate_index_none message randomizer)
                  (fun indexAnswer =>
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    .sign index (fun bottomAnswer =>
                      prependAction (.publicHash input)
                        (eagerCutoffView answers cache
                          (next (signatureFromAnswers cache randomizer index
                            bottomAnswer)) budget)))
              have hbody : annotate body secret = mapView (marked secret) body := by
                dsimp [body]
                apply congrArg (View.privateHash input
                  (locate_index_none message randomizer))
                funext indexAnswer
                let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                apply congrArg (View.sign index)
                funext bottomAnswer
                have zeroCharge :
                    (Action.publicHash input).charge.secretKey = 0 := by
                  simpa [input, Action.charge] using
                    congrArg SecuritySharedBudget.Counts.secretKey
                      (GroupedBalancedGameViewLog67.index_charge message
                        randomizer)
                have hp := prepend_marked (.publicHash input)
                  (eagerCutoffView answers cache
                    (next (signatureFromAnswers cache randomizer index
                      bottomAnswer)) budget) secret
                  (by simpa [zeroCharge] using (ih
                    (signatureFromAnswers cache randomizer index
                      bottomAnswer) budget secret))
                simpa [zeroCharge] using hp
              have hp := prepend_marked .privateHash body secret
                (by simpa [Action.charge] using hbody)
              simpa only [eagerCutoffView, Action.charge, Nat.add_zero,
                body, randomizer, input] using hp

#print axioms eager_log_count

end SigGolfCandidate.Hypertree.GroupedBalancedEagerLogCount67
