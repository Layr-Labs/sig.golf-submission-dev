import SigGolfCandidate.Hypertree.GroupedBalancedVerifierCache67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedVerifierReplay67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedVerifierExposure67. -/
section
/-! Every completed contact-free verifier step replays under the fixed
programmed graph oracle and any total residual hash extending its final cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierReplay67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorCompose67
open GroupedBalancedGraphMonitorPublicCoupling67
open GroupedBalancedVerifierCache67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def programmed (table : PointTable) (base : Hash) : Hash :=
  GroupedBalancedGraphProgramming67.programmed
    (GroupedBalancedGraphPayload67.payload
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table))
    (GroupedBalancedGraphMonitorTable67.labelsOf table) base

theorem query_support_agrees (table : PointTable)
    (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((GroupedBalancedGraphOracle67.publicOracle
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache))
    (base : Hash) (agree : result.2.AgreesWithFn base) :
    cache.AgreesWithFn base ∧ programmed table base query = result.1 := by
  have old : cache.AgreesWithFn base := by
    intro other value present
    exact agree (GroupedBalancedVerifierCache67.query_preserves table
      query cache result member other value present)
  constructor
  · exact old
  · rw [programmed,
      GroupedBalancedGraphOracle67.programmed_hash]
    cases canonical : GroupedBalancedGraphOracle67.canonical
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) query with
    | some answer =>
        simp only [GroupedBalancedGraphOracle67.publicOracle,
          canonical, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at member
        subst result
        simp only [canonical]
    | none =>
        simp only [GroupedBalancedGraphOracle67.publicOracle,
          canonical] at member
        have present := GroupedBalancedVerifierCache67.random_present
          query cache result member
        simpa only [canonical] using agree present

theorem completed_eval {α : Type} (table : PointTable)
    (signed : Finset (BitVec 160))
    (program : OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result α)
    (member : some result ∈ support
      (stopped table exposed (compile program exposed cache)))
    (base : Hash) (agree : result.2.2.AgreesWithFn base) :
    cache.AgreesWithFn base ∧
      evalWithAnswerFn (programmed table base) program = result.1 ∧
      Safe table signed result.2.1 result.2.2 := by
  induction program using OracleComp.inductionOn
      generalizing exposed cache result with
  | pure value =>
      simp only [compile_pure, stopped, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact ⟨agree, rfl, initial⟩
  | query_bind query next ih =>
      rw [compile_query,
        stopped_public_bind table signed exposed cache initial,
        mem_support_bind_iff] at member
      obtain ⟨read, queried, tail⟩ := member
      cases read with
      | none =>
          simp only [continueWith, support_pure,
            Set.mem_singleton_iff, Option.some_ne_none] at tail
      | some answer =>
          have spec := read_spec table signed exposed cache initial query
            answer queried
          have nextSafe :=
            GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
              table signed exposed cache initial query answer queried
          have later := ih answer.1 answer.2.1 answer.2.2
            nextSafe result tail agree
          have replay := query_support_agrees table query cache
            (answer.1, answer.2.2) spec.2.2.2 base later.1
          refine ⟨replay.1, ?_, later.2.2⟩
          change evalWithAnswerFn (programmed table base)
            (next (programmed table base query)) = result.1
          rw [replay.2]
          exact later.2.1

#print axioms query_support_agrees
#print axioms completed_eval

end SigGolfCandidate.Hypertree.GroupedBalancedVerifierReplay67

end

/-! Public graph exposure grows during a completed verifier run, so a point
still hidden at the end was hidden at every preceding query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierExposure67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorCompose67
open GroupedBalancedGraphMonitorPublicCoupling67
open GroupedBalancedVerifierCache67
open GroupedBalancedVerifierReplay67
open SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def Extends (earlier later : QueryCache PointSpec) : Prop :=
  ∀ point, earlier point ≠ none → later point ≠ none

theorem extends_refl (cache : QueryCache PointSpec) :
    Extends cache cache := by
  intro point present
  exact present

theorem extends_trans (first second third : QueryCache PointSpec)
    (h1 : Extends first second) (h2 : Extends second third) :
    Extends first third := by
  intro point present
  exact h2 point (h1 point present)

theorem cacheQuery_extends (cache : QueryCache PointSpec)
    (target : Point) (answer : BitVec 256) :
    Extends cache (cache.cacheQuery target answer) := by
  intro point present
  by_cases same : point = target
  · subst point
    rw [QueryCache.cacheQuery_self]
    exact Option.some_ne_none _
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    exact present

theorem revealCache_extends (table : PointTable) (points : List Point)
    (cache : QueryCache PointSpec) :
    Extends cache
      (GroupedBalancedGraphMonitorOracle67.revealCache table points cache) := by
  induction points generalizing cache with
  | nil => exact extends_refl cache
  | cons point rest ih =>
      exact extends_trans cache
        (cache.cacheQuery point (table point)) _
        (cacheQuery_extends cache point (table point))
        (ih (cache.cacheQuery point (table point)))

theorem opened_extends (table : PointTable)
    (cache : QueryCache PointSpec) (query : Query) :
    Extends cache
      (GroupedBalancedGraphMonitorPublicCoupling67.opened
        table cache query) := by
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simpa only [GroupedBalancedGraphMonitorPublicCoupling67.opened,
        located] using extends_refl cache
  | some position =>
      by_cases two : position.val.tag.val = 2
      · by_cases canonical : query =
            GroupedBalancedGraphCausality67.graphInput
              (GroupedBalancedGraphMonitorTable67.privateOf table)
              (GroupedBalancedGraphMonitorTable67.labelsOf table) position
        · simpa only [GroupedBalancedGraphMonitorPublicCoupling67.opened,
            located, if_pos two, if_pos canonical] using
            (cacheQuery_extends cache (.inl position) (table (.inl position)))
        · simpa only [GroupedBalancedGraphMonitorPublicCoupling67.opened,
            located, if_pos two, if_neg canonical] using
            (extends_refl cache)
      · let metadata := GroupedBalancedGraphMonitorOracle67.revealCache
          table (GroupedBalancedGraphMonitorOracle67.required position) cache
        have hmeta : Extends cache metadata :=
          revealCache_extends table _ cache
        by_cases canonical : query =
            GroupedBalancedGraphCausality67.graphInput
              (GroupedBalancedGraphMonitorTable67.privateOf table)
              (GroupedBalancedGraphMonitorTable67.labelsOf table) position
        · simpa only [GroupedBalancedGraphMonitorPublicCoupling67.opened,
            located, if_neg two, if_pos canonical, metadata] using
            (extends_trans cache metadata _ hmeta
              (cacheQuery_extends metadata (.inl position)
                (table (.inl position))))
        · simpa only [GroupedBalancedGraphMonitorPublicCoupling67.opened,
            located, if_neg two, if_neg canonical, metadata] using hmeta

theorem completed_extends {α : Type} (table : PointTable)
    (signed : Finset (BitVec 160))
    (program : OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result α)
    (member : some result ∈ support
      (stopped table exposed (compile program exposed cache))) :
    Extends exposed result.2.1 := by
  induction program using OracleComp.inductionOn
      generalizing exposed cache result with
  | pure value =>
      simp only [compile_pure, stopped, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact extends_refl exposed
  | query_bind query next ih =>
      rw [compile_query,
        stopped_public_bind table signed exposed cache initial,
        mem_support_bind_iff] at member
      obtain ⟨read, queried, tail⟩ := member
      cases read with
      | none =>
          simp only [continueWith, support_pure,
            Set.mem_singleton_iff, Option.some_ne_none] at tail
      | some answer =>
          have spec := read_spec table signed exposed cache initial query
            answer queried
          have nextSafe :=
            GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
              table signed exposed cache initial query answer queried
          have firstExt : Extends exposed answer.2.1 := by
            rw [spec.2.2.1]
            exact opened_extends table exposed query
          exact extends_trans exposed answer.2.1
            result.2.1 firstExt
            (ih answer.1 answer.2.1 answer.2.2 nextSafe result tail)

theorem inputHit_of_later (table : PointTable)
    (earlier later : QueryCache PointSpec)
    (extension : Extends earlier later) (query : Query)
    (hit : inputHit table later query) :
    inputHit table earlier query := by
  unfold inputHit at hit ⊢
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [located] at hit
  | some position =>
      simp only [located] at hit ⊢
      by_cases chain : position.val.tag.val = 2
      · simp only [if_pos chain] at hit ⊢
        cases previous : GroupedBalancedGraphMonitorPredecessor67.predecessor
            position.val with
        | none =>
            simp only [previous] at hit
        | some point =>
            simp only [previous] at hit ⊢
            refine ⟨?_, hit.2⟩
            by_cases found : earlier point = none
            · exact found
            · have prior : earlier point ≠ none := found
              have known := extension point prior
              exact False.elim (known hit.1)
      · simpa only [if_neg chain] using hit

theorem completed_no_contacts {α : Type} (table : PointTable)
    (signed : Finset (BitVec 160))
    (program : OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result α)
    (member : some result ∈ support
      (stopped table exposed (compile program exposed cache)))
    (base : Hash) (agree : result.2.2.AgreesWithFn base) :
    ∀ query ∈ queries (programmed table base) program,
      ¬inputHit table result.2.1 query ∧
        ¬outputHit table query (programmed table base query) := by
  induction program using OracleComp.inductionOn
      generalizing exposed cache result with
  | pure value =>
      intro query present
      simp only [queries_pure, List.not_mem_nil] at present
  | query_bind input next ih =>
      have original := member
      rw [compile_query,
        stopped_public_bind table signed exposed cache initial,
        mem_support_bind_iff] at member
      obtain ⟨read, queried, tail⟩ := member
      cases read with
      | none =>
          simp only [continueWith, support_pure,
            Set.mem_singleton_iff, Option.some_ne_none] at tail
      | some answer =>
          have spec := read_spec table signed exposed cache initial input
            answer queried
          have nextSafe :=
            GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
              table signed exposed cache initial input answer queried
          have later := ih answer.1 answer.2.1 answer.2.2
            nextSafe result tail agree
          have replay := query_support_agrees table input cache
            (answer.1, answer.2.2) spec.2.2.2 base
            ((completed_eval table signed (next answer.1)
              answer.2.1 answer.2.2 nextSafe result tail base agree).1)
          have extension : Extends exposed result.2.1 := by
            apply completed_extends table signed
              (liftM (HashSpec.query input) >>= next)
              exposed cache initial result
            exact original
          intro query present
          rw [queries_query_bind, replay.2] at present
          rcases List.mem_cons.mp present with same | tailMember
          · subst query
            exact ⟨fun hit => spec.1
                (inputHit_of_later table exposed result.2.1
                  extension input hit),
              by simpa only [replay.2] using spec.2.1⟩
          · exact later query tailMember

#print axioms completed_extends
#print axioms completed_no_contacts

end SigGolfCandidate.Hypertree.GroupedBalancedVerifierExposure67
