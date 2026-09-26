import SigGolfCandidate.Hypertree.GroupedBalancedPrivateLegacyEligible67
import SigGolfCandidate.Hypertree.GroupedBalancedGameQueryTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSignCoupling67
import SigGolfCandidate.Hypertree.GroupedBalancedGameViewLoggedBridge67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifierCache67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
import SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedStoppedMapView67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67. -/
section
/-! Naturality of the stopped graph interpreter under pure maps of a View's
terminal value. The cutoff and graph-contact flags are preserved exactly. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedStoppedMapView67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGameViewLoggedBridge67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def mapResult {α β : Type} (f : α → β) :
    Option (Option α × Nat × State) →
      Option (Option β × Nat × State)
  | none => none
  | some (value, remaining, state) =>
      some (value.map f, remaining, state)

theorem execute_mapView {α β : Type} (table : PointTable)
    (f : α → β) (view : View α)
    (remaining : Nat) (state : State) :
    execute table (mapView f view) remaining state =
      mapResult f <$> execute table view remaining state := by
  induction view generalizing remaining state with
  | done value => rfl
  | coin n next ih =>
      simp only [mapView, execute, map_bind]
      exact bind_congr fun answer => ih answer remaining state
  | sign index next ih =>
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index))))
  | privateHash input outside next ih =>
      cases present : state.residual input with
      | some answer =>
          simp only [mapView, execute, present]
          exact ih answer remaining state
      | none =>
          simp only [mapView, execute, present, map_bind]
          exact bind_congr fun answer =>
            ih answer remaining (privateOpened state input answer)
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [mapView, execute]
          by_cases first :
              GroupedBalancedGraphMonitorPublicCoupling67.inputHit
                table state.exposed input
          · simp only [if_pos first, map_pure, mapResult]
          · simp only [if_neg first, map_bind]
            apply bind_congr
            intro answer
            by_cases second :
                GroupedBalancedGraphMonitorPublicCoupling67.outputHit
                  table input answer.1
            · simp only [if_pos second, map_pure, mapResult]
            · simp only [if_neg second]
              exact ih answer.1 remaining
                (opened state
                  (GroupedBalancedGraphMonitorPublicCoupling67.opened
                    table state.exposed input) answer.2)

#print axioms execute_mapView

end SigGolfCandidate.Hypertree.GroupedBalancedStoppedMapView67
end

/-! Any logged public query at a direct67 private-source input triggers the
already-budgeted secret-key hit event for the sampled key. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPrivateHitFromLog67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedGameQueryTrace67
set_option backward.isDefEq.respectTransparency false

theorem public_mem_secretInputs (trace : List Action) (query : Query)
    (member : Action.publicHash query ∈ trace)
    (eligible : SecuritySeparation.SecretKeyEligible query) :
    query ∈ secretInputs trace := by
  induction trace with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst head
        simp only [secretInputs, if_pos eligible]
        exact List.mem_cons_self
      · cases head with
        | privateHash =>
            simpa only [secretInputs] using ih later
        | publicHash input =>
            by_cases inputEligible : SecuritySeparation.SecretKeyEligible input
            · simp only [secretInputs, if_pos inputEligible]
              exact List.mem_cons_of_mem _ (ih later)
            · simpa only [secretInputs, if_neg inputEligible] using ih later

theorem private_query_hit (secretKey : SecretKey)
    (slot : GroupedBalancedPrivateDerivation67.Slot)
    (trace : List Action)
    (member : Action.publicHash
      (GroupedBalancedPrivateDerivation67.input secretKey slot) ∈ trace) :
    SecuritySecretKey.SecretKeyHitTrace (secretInputs trace) secretKey := by
  let query := GroupedBalancedPrivateDerivation67.input secretKey slot
  have eligible :=
    GroupedBalancedPrivateLegacyEligible67.eligible_of_direct secretKey slot
  have queried : query ∈ secretInputs trace :=
    public_mem_secretInputs trace query member eligible
  exact ⟨query, queried,
    GroupedBalancedPrivateDerivation67.input_secretKeyAt secretKey slot⟩

#print axioms private_query_hit

end SigGolfCandidate.Hypertree.GroupedBalancedPrivateHitFromLog67


/-! A private-source input can enter the stopped residual oracle cache only
through an adversarial public query at that exact input. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem random_absent_of_ne (query old : Query)
    (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((randomOracle (spec := HashSpec) query).run cache))
    (different : old ≠ query) (absent : cache old = none) :
    result.2 old = none := by
  cases found : cache query with
  | some answer =>
      simp only [randomOracle.run_eq, found, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      exact absent
  | none =>
      simp only [randomOracle.run_eq, found, bind_pure_comp,
        support_map, Set.mem_image] at member
      obtain ⟨answer, _, same⟩ := member
      cases same
      simpa only [QueryCache.cacheQuery_of_ne _ _ different] using absent

theorem query_absent_of_ne (table : PointTable)
    (query old : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((GroupedBalancedGraphOracle67.publicOracle
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache))
    (different : old ≠ query) (absent : cache old = none) :
    result.2 old = none := by
  cases canonical : GroupedBalancedGraphOracle67.canonical
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) query with
  | some answer =>
      simp only [GroupedBalancedGraphOracle67.publicOracle, canonical,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact absent
  | none =>
      simp only [GroupedBalancedGraphOracle67.publicOracle, canonical] at member
      exact random_absent_of_ne query old cache result member different absent

theorem prepend_member {α : Type} (table : PointTable)
    (action : Action) (view : View (Option α × List Action))
    (remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, action :: trace), left, final) ∈ support
      (execute table (prependAction action view) remaining state)) :
    some (some (value, trace), left, final) ∈ support
      (execute table view remaining state) := by
  rw [prependAction, GroupedBalancedStoppedMapView67.execute_mapView,
    support_map] at member
  obtain ⟨source, sourceMember, same⟩ := member
  cases source with
  | none => cases same
  | some source =>
      rcases source with ⟨maybe, left', final'⟩
      cases maybe with
      | none => cases same
      | some pair =>
          rcases pair with ⟨value', trace'⟩
          simp only [GroupedBalancedStoppedMapView67.mapResult,
            Option.map_some] at same
          cases same
          exact sourceMember

theorem prepend_decompose {α : Type} (table : PointTable)
    (action : Action) (view : View (Option α × List Action))
    (remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table (prependAction action view) remaining state)) :
    ∃ tail, trace = action :: tail ∧
      some (some (value, tail), left, final) ∈ support
        (execute table view remaining state) := by
  rw [prependAction, GroupedBalancedStoppedMapView67.execute_mapView,
    support_map] at member
  obtain ⟨source, sourceMember, same⟩ := member
  cases source with
  | none => cases same
  | some source =>
      rcases source with ⟨maybe, left', final'⟩
      cases maybe with
      | none => cases same
      | some pair =>
          rcases pair with ⟨value', tail⟩
          simp only [GroupedBalancedStoppedMapView67.mapResult,
            Option.map_some] at same
          cases same
          exact ⟨tail, rfl, sourceMember⟩

theorem private_step {α : Type} (table : PointTable)
    (input old : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α) (remaining : Nat)
    (state : State) (target : Option (Option α × Nat × State))
    (different : old ≠ input) (absent : state.residual old = none)
    (member : target ∈ support
      (execute table (.privateHash input outside next) remaining state)) :
    ∃ answer nextState,
      target ∈ support (execute table (next answer) remaining nextState) ∧
      nextState.residual old = none := by
  cases present : state.residual input with
  | some answer =>
      exact ⟨answer, state, by simpa only [execute, present] using member,
        absent⟩
  | none =>
      simp only [execute, present, mem_support_bind_iff] at member
      obtain ⟨answer, _, tail⟩ := member
      refine ⟨answer, privateOpened state input answer, tail, ?_⟩
      simpa only [privateOpened,
        QueryCache.cacheQuery_of_ne _ _ different] using absent

theorem hash_step {α : Type} (table : PointTable)
    (input old : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state final : State) (value : α)
    (left : Nat)
    (member : some (some value, left, final) ∈ support
      (execute table (.hash input next) (remaining + 1) state)) :
    ∃ answer nextState,
      some (some value, left, final) ∈ support
        (execute table (next answer) remaining nextState) ∧
      (old ≠ input → state.residual old = none →
        nextState.residual old = none) := by
  simp only [execute] at member
  by_cases hit : GroupedBalancedGraphMonitorPublicCoupling67.inputHit
      table state.exposed input
  · simp only [if_pos hit, support_pure,
      Set.mem_singleton_iff, Option.some_ne_none] at member
  · simp only [if_neg hit, mem_support_bind_iff] at member
    obtain ⟨read, readMember, tail⟩ := member
    by_cases second : GroupedBalancedGraphMonitorPublicCoupling67.outputHit
        table input read.1
    · simp only [if_pos second, support_pure,
        Set.mem_singleton_iff, Option.some_ne_none] at tail
    · simp only [if_neg second] at tail
      refine ⟨read.1,
        opened state
          (GroupedBalancedGraphMonitorPublicCoupling67.opened table
            state.exposed input) read.2, tail, ?_⟩
      intro different absent
      exact query_absent_of_ne table input old state.residual read
        readMember different absent

theorem eager_no_action_absent {α : Type}
    (secretKey : SecretKey)
    (slot : GroupedBalancedPrivateDerivation67.Slot)
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (publicCache : QueryCache PointSpec)
    (interaction : GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers publicCache interaction budget)
        remaining state))
    (absent : state.residual
      (GroupedBalancedPrivateDerivation67.input secretKey slot) = none)
    (unqueried : Action.publicHash
      (GroupedBalancedPrivateDerivation67.input secretKey slot) ∉ trace) :
    final.residual
      (GroupedBalancedPrivateDerivation67.input secretKey slot) = none := by
  induction interaction generalizing budget remaining state value trace with
  | done answer =>
      simp only [eagerCutoffView, execute, support_pure,
        Set.mem_singleton_iff] at member
      cases member
      exact absent
  | coin n next ih =>
      simp only [eagerCutoffView, execute,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, tail⟩ := member
      exact ih answer budget remaining state value trace tail absent unqueried
  | hash input next ih =>
      cases budget with
      | zero =>
          simp only [eagerCutoffView, execute, support_pure,
            Set.mem_singleton_iff] at member
          cases member
          exact absent
      | succ budget =>
          cases remaining with
          | zero =>
              simp only [eagerCutoffView, execute, support_pure,
                Set.mem_singleton_iff] at member
              cases member
          | succ remaining =>
              obtain ⟨answer, state', tail, preserves⟩ :=
                hash_step table input
                  (GroupedBalancedPrivateDerivation67.input secretKey slot)
                  (fun answer => prependAction (.publicHash input)
                    (eagerCutoffView answers publicCache (next answer) budget))
                  remaining state final (value, trace) left
                  (by simpa only [eagerCutoffView] using member)
              obtain ⟨tailTrace, traceEq, tailMember⟩ :=
                prepend_decompose table (.publicHash input)
                  (eagerCutoffView answers publicCache (next answer) budget)
                  remaining state' final value trace left tail
              subst trace
              have different :
                  GroupedBalancedPrivateDerivation67.input secretKey slot ≠
                    input := by
                intro equal
                exact unqueried (by simpa only [equal] using
                  (List.mem_cons_self : Action.publicHash input ∈
                    Action.publicHash input :: tailTrace))
              have unqueriedTail : Action.publicHash
                  (GroupedBalancedPrivateDerivation67.input secretKey slot) ∉
                    tailTrace := by
                intro found
                exact unqueried (List.mem_cons_of_mem _ found)
              exact ih answer budget remaining state' value tailTrace
                tailMember
                (preserves different absent) unqueriedTail
  | sign message next ih =>
      cases budget with
      | zero =>
          simp only [eagerCutoffView, execute, support_pure,
            Set.mem_singleton_iff] at member
          cases member
          exact absent
      | succ budget =>
          cases budget with
          | zero =>
              obtain ⟨trace', traceEq, firstMember⟩ :=
                prepend_decompose table .privateHash (.done (none, []))
                  remaining state final value trace left
                  (by simpa only [eagerCutoffView] using member)
              subst trace
              simp only [execute, support_pure,
                Set.mem_singleton_iff] at firstMember
              cases firstMember
              exact absent
          | succ budget =>
              let randomizer := answers (.randomizer message)
              let input := SecurityRandomOracle.indexInput message randomizer
              let old := GroupedBalancedPrivateDerivation67.input secretKey slot
              let branch : View (Option α × List Action) :=
                .privateHash input (locate_index_none message randomizer)
                  (fun indexAnswer =>
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    .sign index (fun bottomAnswer =>
                      prependAction (.publicHash input)
                        (eagerCutoffView answers publicCache
                          (next (signatureFromAnswers publicCache randomizer
                            index bottomAnswer)) budget)))
              have unfolded : eagerCutoffView answers publicCache
                  (.sign message next) (budget + 1 + 1) =
                  prependAction .privateHash branch := by
                rfl
              obtain ⟨trace', traceEq, firstMember⟩ :=
                prepend_decompose table .privateHash branch
                  remaining state final value trace left
                  (by simpa only [unfolded] using member)
              subst trace
              have different : old ≠ input := by
                exact GroupedBalancedQueryClasses67.private_input_ne_index
                  secretKey slot message randomizer
              obtain ⟨indexAnswer, state', secondMember, state'Absent⟩ :=
                private_step table input old
                  (locate_index_none message randomizer)
                  (fun indexAnswer =>
                    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
                    .sign index (fun bottomAnswer =>
                      prependAction (.publicHash input)
                        (eagerCutoffView answers publicCache
                          (next (signatureFromAnswers publicCache randomizer
                            index bottomAnswer)) budget)))
                  remaining state _ different absent
                  (by simpa only [branch] using firstMember)
              let index : BitVec 160 := indexAnswer.extractLsb' 0 160
              let bottomAnswer := table (.inr (.inl index))
              have thirdMember : some
                  (some (value, trace'), left, final) ∈ support
                  (execute table
                    (prependAction (.publicHash input)
                      (eagerCutoffView answers publicCache
                        (next (signatureFromAnswers publicCache randomizer
                          index bottomAnswer)) budget))
                    remaining (signed state' index bottomAnswer)) := by
                simpa only [execute] using secondMember
              obtain ⟨tailTrace, traceEq, tailMember⟩ :=
                prepend_decompose table (.publicHash input)
                  (eagerCutoffView answers publicCache
                    (next (signatureFromAnswers publicCache randomizer
                      index bottomAnswer)) budget)
                  remaining (signed state' index bottomAnswer)
                  final value trace' left thirdMember
              subst trace'
              have unqueriedTail : Action.publicHash old ∉ tailTrace := by
                intro found
                exact unqueried
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ found))
              exact ih (signatureFromAnswers publicCache randomizer index
                  bottomAnswer) budget remaining
                (signed state' index bottomAnswer) value tailTrace tailMember
                (by simpa only [signed] using state'Absent) unqueriedTail

theorem eager_private_fresh {α : Type}
    (secretKey : SecretKey)
    (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (publicCache : QueryCache PointSpec)
    (interaction : GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers publicCache interaction budget)
        remaining state))
    (initialFresh : ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      state.residual (GroupedBalancedPrivateDerivation67.input secretKey slot) = none)
    (noHit : ¬SecuritySecretKey.SecretKeyHitTrace
      (secretInputs trace) secretKey) :
    ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      final.residual (GroupedBalancedPrivateDerivation67.input secretKey slot) = none := by
  intro slot
  apply eager_no_action_absent secretKey slot answers table publicCache
    interaction budget remaining state final value trace left member
    (initialFresh slot)
  intro found
  exact noHit (GroupedBalancedPrivateHitFromLog67.private_query_hit
    secretKey slot trace found)

#print axioms eager_no_action_absent
#print axioms eager_private_fresh

#print axioms query_absent_of_ne
#print axioms prepend_member
#print axioms prepend_decompose
#print axioms private_step
#print axioms hash_step

end SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67
