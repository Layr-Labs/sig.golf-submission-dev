import SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67
import SigGolfCandidate.Hypertree.SecurityGraphIdeal
import SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGameCutoffView67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67. -/
section
/-! The GameWorld total-call cutoff can be reified as a structured monitor
View while preserving the full query-class log even if a call is refused. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameCutoffView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open SecurityGameHop
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem logged_cutoff_query_bind {α : Type}
    (query : GameWorld.Domain)
    (next : GameWorld.Range query → OracleComp GameWorld α)
    (budget : Nat) :
    logged (SecurityBudget.cutoff
      (liftM (GameWorld.query query) >>= next) budget) =
      if SecurityBudget.charge query ≤ budget then (do
        let answer ← liftM (GameWorld.query query)
        let result ← logged
          (SecurityBudget.cutoff (next answer)
            (budget - SecurityBudget.charge query))
        pure (result.1, prepend query result.2))
      else pure (none, []) := by
  rw [SecurityBudget.cutoff_query_bind]
  split
  · exact logged_query_bind _ _
  · rfl

noncomputable def cutoffView {α : Type} (secretKey : SecretKey)
    (cache : QueryCache PointSpec) :
    Interaction α → Nat → View (Option α × List Action)
  | .done value, _ => .done (some value, [])
  | .coin n next, budget => .coin n (fun answer =>
      cutoffView secretKey cache (next answer) budget)
  | .hash _ _, 0 => .done (none, [])
  | .hash input next, budget + 1 =>
      .hash input (fun answer =>
        prependAction (.publicHash input)
          (cutoffView secretKey cache (next answer) budget))
  | .sign _ _, 0 => .done (none, [])
  | .sign message next, budget + 1 =>
      .privateHash (SecurityRandomOracle.randomizerInput secretKey message)
        (locate_randomizer_none secretKey message) (fun randomizer =>
          prependAction .privateHash
            (match budget with
            | 0 => .done (none, [])
            | budget + 1 =>
                let input := SecurityRandomOracle.indexInput message randomizer
                .privateHash input (locate_index_none message randomizer)
                  (fun indexAnswer =>
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    .sign index (fun bottomAnswer =>
                      prependAction (.publicHash input)
                        (cutoffView secretKey cache
                          (next (signatureFromAnswers cache randomizer index
                            bottomAnswer)) budget)))))

theorem resolve_logged_cutoff {α : Type} (secretKey : SecretKey)
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    resolve secretKey
      (logged (SecurityBudget.cutoff
        (gameView table cache interaction) budget)) =
      ofView table (cutoffView secretKey cache interaction budget) := by
  induction interaction generalizing budget with
  | done value =>
      simp only [gameView, SecurityBudget.cutoff_pure, logged_pure,
        cutoffView, ofView, resolve, simulateQ_pure]
  | coin n next ih =>
      simp only [gameView, logged_cutoff_query_bind,
        SecurityBudget.charge, Nat.zero_le, if_pos, Nat.sub_zero,
        prepend, cutoffView, ofView,
        resolve, simulateQ_bind, simulateQ_pure, resolve_coin]
      apply bind_congr
      intro answer
      simpa using ih answer budget
  | hash input next ih =>
      cases budget with
      | zero =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.not_succ_le_zero,
            if_false, cutoffView, ofView,
            resolve, simulateQ_pure]
          simp
      | succ budget =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.le_add_left, if_pos,
            Nat.add_sub_cancel_right, prepend,
            cutoffView, ofView, ofView_prependAction,
            resolve, simulateQ_bind, simulateQ_pure,
            resolve_public]
          apply bind_congr
          intro answer
          simpa only [map_eq_pure_bind] using
            congrArg (fun computation : OracleComp World
                (Option α × List Action) =>
              (fun result =>
                (result.1, Action.publicHash input :: result.2)) <$>
                computation) (ih answer budget)
  | sign message next ih =>
      cases budget with
      | zero =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.not_succ_le_zero,
            if_false, cutoffView, ofView,
            resolve, simulateQ_pure]
          simp
      | succ budget =>
          cases budget with
          | zero =>
              simp only [gameView, logged_cutoff_query_bind,
                SecurityBudget.charge, Nat.le_add_left, if_pos,
                Nat.add_sub_cancel_right, Nat.not_succ_le_zero,
                if_false, prepend,
                cutoffView, ofView, ofView_prependAction,
                resolve, simulateQ_bind, simulateQ_pure,
                resolve_randomizer]
              simp
          | succ budget =>
              simp only [gameView, logged_cutoff_query_bind,
                SecurityBudget.charge, Nat.le_add_left, if_pos,
                Nat.add_sub_cancel_right, prepend,
                cutoffView, ofView, ofView_prependAction,
                resolve, simulateQ_bind, simulateQ_pure,
                resolve_randomizer, resolve_public]
              have rem : budget + 1 + 1 - 1 - 1 = budget := by omega
              simp only [rem, map_bind, map_eq_pure_bind,
                bind_assoc, pure_bind]
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
                congrArg (fun computation : OracleComp World
                    (Option α × List Action) =>
                  (fun result =>
                    (result.1, Action.privateHash ::
                      Action.publicHash input :: result.2)) <$> computation)
                  (ih signature budget)

#print axioms resolve_logged_cutoff

end SigGolfCandidate.Hypertree.GroupedBalancedGameCutoffView67
end

/-! Under an eager independent private-slot table, direct67 honest signing
reads its randomizer from that table and sends only H5 to the public oracle.
This View is suitable for the existing graph/H5 joint monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerView67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open SecurityGameHop SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def eagerView {α : Type} (answers : PrivateTable)
    (cache : QueryCache PointSpec) : Interaction α → View α
  | .done value => .done value
  | .coin n next => .coin n (fun answer =>
      eagerView answers cache (next answer))
  | .hash input next => .hash input (fun answer =>
      eagerView answers cache (next answer))
  | .sign message next =>
      let randomizer := answers (.randomizer message)
      let input := SecurityRandomOracle.indexInput message randomizer
      .privateHash input (locate_index_none message randomizer)
        (fun indexAnswer =>
          let index : BitVec 160 := indexAnswer.extractLsb' 0 160
          .sign index (fun bottomAnswer =>
            eagerView answers cache
              (next (signatureFromAnswers cache randomizer index
                bottomAnswer))))

/-- Exact ideal-game syntax after the private-slot table is sampled. -/
theorem fixPrivate_gameView {α : Type} (answers : PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) :
    fixPrivate answers (gameView table cache interaction) =
      ofView table (eagerView answers cache interaction) := by
  induction interaction with
  | done value => rfl
  | coin n next ih =>
      simp only [gameView, eagerView, ofView, fixPrivate_query,
        privateImplementation]
      exact bind_congr (fun answer => ih answer)
  | hash input next ih =>
      simp only [gameView, eagerView, ofView, fixPrivate_query,
        privateImplementation]
      exact bind_congr (fun answer => ih answer)
  | sign message next ih =>
      simp only [gameView, eagerView, ofView, fixPrivate_query,
        privateImplementation, pure_bind]
      apply bind_congr
      intro indexAnswer
      exact ih _

#print axioms fixPrivate_gameView

end SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerView67


/-! Interpret the ideal GameWorld cutoff with an independently sampled eager
private-slot table. The structured View still logs the charged typed tag6
read, while only H5 and adversarial hashes reach the public oracle. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedGameCutoffView67
open SecurityGameHop SecurityGraphIdeal
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem fixPrivate_map {α β : Type} (answers : PrivateTable)
    (f : α → β) (program : OracleComp GameWorld α) :
    fixPrivate answers (f <$> program) =
      f <$> fixPrivate answers program := by
  simp only [fixPrivate, simulateQ_map]

theorem fixPrivate_public_step {α : Type} (answers : PrivateTable)
    (input : Query) (next : BitVec 256 → OracleComp GameWorld α) :
    fixPrivate answers (liftM (GameWorld.query (.inr (.inr input))) >>= next) =
      (do
        let answer ← liftM (World.query (.inr input))
        fixPrivate answers (next answer)) := by
  exact fixPrivate_query answers (.inr (.inr input)) next

noncomputable def eagerCutoffView {α : Type} (answers : PrivateTable)
    (cache : QueryCache PointSpec) :
    Interaction α → Nat → View (Option α × List Action)
  | .done value, _ => .done (some value, [])
  | .coin n next, budget => .coin n (fun answer =>
      eagerCutoffView answers cache (next answer) budget)
  | .hash _ _, 0 => .done (none, [])
  | .hash input next, budget + 1 =>
      .hash input (fun answer =>
        prependAction (.publicHash input)
          (eagerCutoffView answers cache (next answer) budget))
  | .sign _ _, 0 => .done (none, [])
  | .sign message next, budget + 1 =>
      let randomizer := answers (.randomizer message)
      prependAction .privateHash
        (match budget with
        | 0 => .done (none, [])
        | budget + 1 =>
            let input := SecurityRandomOracle.indexInput message randomizer
            .privateHash input (locate_index_none message randomizer)
              (fun indexAnswer =>
                let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                .sign index (fun bottomAnswer =>
                  prependAction (.publicHash input)
                    (eagerCutoffView answers cache
                      (next (signatureFromAnswers cache randomizer index
                        bottomAnswer)) budget))))

/-- The entire stopped ideal action log, including cutoff branches, is the
eager private-slot View's public-oracle interpretation. -/
theorem fixPrivate_logged_cutoff {α : Type} (answers : PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (interaction : Interaction α) (budget : Nat) :
    fixPrivate answers
      (logged (SecurityBudget.cutoff
        (gameView table cache interaction) budget)) =
      ofView table (eagerCutoffView answers cache interaction budget) := by
  induction interaction generalizing budget with
  | done value =>
      simp only [gameView, SecurityBudget.cutoff_pure, logged_pure,
        eagerCutoffView, ofView, fixPrivate, simulateQ_pure]
  | coin n next ih =>
      simp only [gameView, logged_cutoff_query_bind,
        SecurityBudget.charge, Nat.zero_le, if_pos, Nat.sub_zero,
        prepend, eagerCutoffView, ofView, fixPrivate_query,
        privateImplementation]
      apply bind_congr
      intro answer
      simpa using ih answer budget
  | hash input next ih =>
      cases budget with
      | zero =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.not_succ_le_zero,
            if_false, eagerCutoffView, ofView,
            fixPrivate, simulateQ_pure]
          simp
      | succ budget =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.le_add_left, if_pos,
            Nat.add_sub_cancel_right, prepend,
            eagerCutoffView, ofView, ofView_prependAction,
            fixPrivate_query, privateImplementation]
          apply bind_congr
          intro answer
          rw [← map_eq_pure_bind, fixPrivate_map, ih answer budget]
  | sign message next ih =>
      cases budget with
      | zero =>
          simp only [gameView, logged_cutoff_query_bind,
            SecurityBudget.charge, Nat.not_succ_le_zero,
            if_false, eagerCutoffView, ofView,
            fixPrivate, simulateQ_pure]
          simp
      | succ budget =>
          cases budget with
          | zero =>
              simp only [gameView, logged_cutoff_query_bind,
                SecurityBudget.charge, Nat.le_add_left, if_pos,
                Nat.add_sub_cancel_right, Nat.not_succ_le_zero,
                if_false, prepend,
                eagerCutoffView, ofView, ofView_prependAction,
                fixPrivate_query, privateImplementation,
                pure_bind]
              simp [fixPrivate]
          | succ budget =>
              simp only [gameView, logged_cutoff_query_bind,
                SecurityBudget.charge, Nat.le_add_left, if_pos,
                Nat.add_sub_cancel_right, prepend,
                eagerCutoffView, ofView, ofView_prependAction]
              rw [fixPrivate_query]
              simp only [privateImplementation, pure_bind]
              simp only [bind_assoc]
              rw [fixPrivate_public_step]
              have rem : budget + 1 + 1 - 1 - 1 = budget := by omega
              simp only [rem, map_bind, map_eq_pure_bind,
                bind_assoc, pure_bind]
              apply bind_congr
              intro indexAnswer
              let randomizer := answers (.randomizer message)
              let input := SecurityRandomOracle.indexInput message randomizer
              let index : BitVec 160 := indexAnswer.extractLsb' 0 160
              let signature := signatureFromAnswers cache randomizer index
                (table (.inr (.inl index)))
              rw [← map_eq_pure_bind, fixPrivate_map,
                ih signature budget]
              simp only [Functor.map_map, Function.comp_def,
                map_eq_pure_bind, bind_assoc, pure_bind]
              rfl

#print axioms fixPrivate_logged_cutoff

end SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
