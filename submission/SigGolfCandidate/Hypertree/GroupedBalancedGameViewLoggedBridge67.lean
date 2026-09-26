import SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67
import SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGameViewLog67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67. -/
section
/-! Expose the exact full-H log of the abstract direct67 organizer. Every
honest signature records one typed randomizer H and one public H5 index H. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameViewLog67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem logged_done {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (value : α) :
    logged (gameView table cache (.done value)) = pure (value, []) := rfl

theorem logged_coin {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (n : Nat)
    (next : Fin (n + 1) → Interaction α) :
    logged (gameView table cache (.coin n next)) = (do
      let answer ← liftM (GameWorld.query (.inl n))
      logged (gameView table cache (next answer))) := by
  simp only [gameView, logged_query_bind, prepend]
  apply bind_congr
  intro answer
  simp

theorem logged_hash {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (input : Query)
    (next : BitVec 256 → Interaction α) :
    logged (gameView table cache (.hash input next)) = (do
      let answer ← liftM (GameWorld.query (.inr (.inr input)))
      let result ← logged (gameView table cache (next answer))
      pure (result.1, .publicHash input :: result.2)) := by
  simp only [gameView, logged_query_bind, prepend]

theorem logged_sign {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (message : Message)
    (next : GroupedBalancedScheme67.Signature → Interaction α) :
    logged (gameView table cache (.sign message next)) = (do
      let randomizer ← liftM
        (GameWorld.query (.inr (.inl (.randomizer message))))
      let input := SecurityRandomOracle.indexInput message randomizer
      let indexAnswer ← liftM (GameWorld.query (.inr (.inr input)))
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let signature := signatureFromAnswers cache randomizer index
        (table (.inr (.inl index)))
      let result ← logged (gameView table cache (next signature))
      pure (result.1,
        .privateHash :: .publicHash input :: result.2)) := by
  simp only [gameView, logged_query_bind, prepend, bind_assoc, pure_bind]

theorem index_charge (message : Message) (randomizer : Bytes 32) :
    GroupedBalancedQueryClasses67.charge
      (SecurityRandomOracle.indexInput message randomizer) = ⟨0, 0, 1⟩ := by
  let input := SecurityRandomOracle.indexInput message randomizer
  have parsed : (SecurityIndexQuery.parse input).isSome = true := by
    simp [input]
  have notSecret : ¬SecuritySeparation.SecretKeyEligible input := by
    intro eligible
    have absent := GroupedBalancedQueryClasses67.legacy_eligible_parse_none
      input eligible
    simp [input] at absent
  have noGraph := GroupedBalancedQueryClasses67.parsed_locate_none
    input parsed
  simp [GroupedBalancedQueryClasses67.charge, input, notSecret,
    noGraph]

theorem sign_counts (message : Message) (randomizer : Bytes 32)
    (trace : List Action) :
    counts (.privateHash ::
      .publicHash (SecurityRandomOracle.indexInput message randomizer) ::
        trace) =
      { (counts trace) with index := (counts trace).index + 1 } := by
  have charge := index_charge message randomizer
  simp only [counts, Action.charge, charge]
  cases counts trace
  simp [Nat.add_comm]

#print axioms logged_sign
#print axioms index_charge
#print axioms sign_counts

end SigGolfCandidate.Hypertree.GroupedBalancedGameViewLog67

end

/-! The exact GameWorld hash-query log is a structured monitor View after
resolving the typed randomizer slot. It keeps the honest H5 query public. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLog67
open SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def mapView {α β : Type} (f : α → β) : View α → View β
  | .done value => .done (f value)
  | .coin n next => .coin n (fun answer => mapView f (next answer))
  | .sign index next => .sign index (fun answer => mapView f (next answer))
  | .hash input next => .hash input (fun answer => mapView f (next answer))
  | .privateHash input outside next =>
      .privateHash input outside (fun answer => mapView f (next answer))

theorem ofView_mapView {α β : Type} (table : PointTable)
    (f : α → β) (view : View α) :
    ofView table (mapView f view) = f <$> ofView table view := by
  induction view with
  | done value => rfl
  | coin n next ih =>
      simp only [mapView, ofView, map_bind]
      exact bind_congr (fun answer => ih answer)
  | sign index next ih =>
      exact ih (table (.inr (.inl index)))
  | hash input next ih =>
      simp only [mapView, ofView, map_bind]
      exact bind_congr (fun answer => ih answer)
  | privateHash input outside next ih =>
      simp only [mapView, ofView, map_bind]
      exact bind_congr (fun answer => ih answer)

noncomputable def prependAction {α : Type} (action : Action) :
    View (α × List Action) → View (α × List Action) :=
  mapView (fun result => (result.1, action :: result.2))

theorem ofView_prependAction {α : Type} (table : PointTable)
    (action : Action) (view : View (α × List Action)) :
    ofView table (prependAction action view) =
      (fun result => (result.1, action :: result.2)) <$> ofView table view :=
  ofView_mapView table _ view

noncomputable def loggedView {α : Type} (secretKey : SecretKey)
    (cache : QueryCache PointSpec) : Interaction α →
      View (α × List Action)
  | .done value => .done (value, [])
  | .coin n next => .coin n (fun answer =>
      loggedView secretKey cache (next answer))
  | .hash input next => .hash input (fun answer =>
      prependAction (.publicHash input)
        (loggedView secretKey cache (next answer)))
  | .sign message next =>
      .privateHash (SecurityRandomOracle.randomizerInput secretKey message)
        (locate_randomizer_none secretKey message) (fun randomizer =>
          let input := SecurityRandomOracle.indexInput message randomizer
          .privateHash input (locate_index_none message randomizer)
            (fun indexAnswer =>
              let index : BitVec 160 := indexAnswer.extractLsb' 0 160
              .sign index (fun bottomAnswer =>
                prependAction .privateHash
                  (prependAction (.publicHash input)
                    (loggedView secretKey cache
                      (next (signatureFromAnswers cache randomizer index
                        bottomAnswer)))))))

/-- Resolved GameWorld action logging is exactly the annotated monitor View,
including both honest signing calls and every adaptive public query. -/
theorem resolve_logged_gameView {α : Type} (secretKey : SecretKey)
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) :
    resolve secretKey (logged (gameView table cache interaction)) =
      ofView table (loggedView secretKey cache interaction) := by
  induction interaction with
  | done value => rfl
  | coin n next ih =>
      rw [logged_coin]
      simp only [resolve, simulateQ_bind, simulateQ_query,
        loggedView, ofView]
      exact bind_congr (fun answer => ih answer)
  | hash input next ih =>
      rw [logged_hash]
      simp only [resolve, simulateQ_bind, simulateQ_pure,
        resolve_public, loggedView, ofView, ofView_prependAction]
      apply bind_congr
      intro answer
      simpa only [map_eq_pure_bind] using
        congrArg (fun computation : OracleComp World (α × List Action) =>
          (fun result => (result.1, Action.publicHash input :: result.2)) <$>
            computation) (ih answer)
  | sign message next ih =>
      rw [logged_sign]
      simp only [resolve, simulateQ_bind, simulateQ_pure,
        resolve_randomizer, resolve_public,
        loggedView, ofView, ofView_prependAction]
      apply bind_congr
      intro randomizer
      apply bind_congr
      intro indexAnswer
      let input := SecurityRandomOracle.indexInput message randomizer
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let signature := signatureFromAnswers cache randomizer index
        (table (.inr (.inl index)))
      simpa only [Functor.map_map, Function.comp_def,
        map_eq_pure_bind, bind_assoc, pure_bind] using
        congrArg (fun computation : OracleComp World (α × List Action) =>
          (fun result =>
            (result.1, Action.privateHash ::
              Action.publicHash input :: result.2)) <$> computation)
          (ih signature)

#print axioms ofView_mapView
#print axioms resolve_logged_gameView

end SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67
