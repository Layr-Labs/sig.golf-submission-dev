import SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicState
import SigGolfCandidate.Hypertree.SecurityGraphTraceContact

/-! Inlined from SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling; its only importer was SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact. -/
section
namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphPublicMonitor SecurityGraphMonitorProgram
  SecurityGraphMonitorCoupling SecurityGraphMonitorInvariant SecurityGraphMonitorMetadata
  SecurityGraphMonitorChainState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- First-contact predicates inspect the sampled graph only in the stopped
coupling. The operational passive compiler never branches on either predicate. -/
def inputHit (factors : Factors) (exposed : QueryCache PointSpec) (query : Query) : Prop :=
  match locate query with
  | some (.chain address step) => exposed (predecessor address step) = none ∧
      query = (Position.chain address step).input (privateTable factors) (labels factors)
  | _ => False

def outputHit (factors : Factors) (query : Query) (answer : BitVec 256) : Prop :=
  match locate query with
  | none => False
  | some position => query ≠ position.input (privateTable factors) (labels factors) ∧
      truncate answer = truncate (labels factors position)

noncomputable def opened (factors : Factors) (exposed : QueryCache PointSpec) (query : Query) :
    QueryCache PointSpec :=
  match locate query with
  | none => exposed
  | some (.chain address step) =>
      if query = (Position.chain address step).input (privateTable factors) (labels factors) then
        exposed.cacheQuery (successor address step) (factors.1 (successor address step))
      else exposed
  | some position => revealCache factors.1 (required position) exposed

/-- Exact stopped coupling of one public call through the actual explicit graph
oracle, retaining the arbitrary continuation and both caches. -/
theorem stopped_public_oracle {α : Type} (factors : Factors) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree factors.1 exposed) (clean : ResidualSafe factors cache) :
    stopped factors.1 exposed (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query next) =
      (if inputHit factors exposed query then pure none else do
        let result ← (SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache
        if outputHit factors query result.1 then pure none
        else (stopped factors.1 (opened factors exposed query)
          (next result.1 (opened factors exposed query) result.2))) := by
  cases located : locate query with
  | none =>
    simp only [inputHit, outputHit, opened, located, if_false]
    exact stopped_public_outside _ factors.2.1 _ _ _ _ _ located
  | some position =>
    cases position with
    | chain address step =>
      have dispatch : SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query next =
          SecurityGraphMonitorOracle.chainStep exposed cache address step query next := by
        simp only [SecurityGraphMonitorOracle.publicStep, located]
      rw [dispatch, stopped_chain _ _ _ _ _ _ _ agree (clean.chain factors cache query address step located)]
      have payload := canonical_chain_input factors address step
      unfold chainStopped
      simp only [inputHit, outputHit, opened, SecurityGraphOracle.publicOracle,
        SecurityGraphOracle.canonical, located, payload]
      by_cases canonical : query = SecurityGraphContact.chainInput address step
          (truncate (factors.1 (predecessor address step)))
      · by_cases hidden : exposed (predecessor address step) = none
        · simp only [canonical, hidden, true_and, and_true, if_true]
        · simp only [canonical, hidden, false_and, if_false, if_true, not_true_eq_false,
            StateT.run_pure, pure_bind]
          simp only [ne_eq, not_true_eq_false, eq_self, false_and, if_false]
          rfl
      · simp only [canonical, and_false, if_false, not_false_eq_true, true_and]
        simp only [ne_eq, canonical, not_false_eq_true, true_and]
        rfl
    | leaf level tree side =>
      have localClean : CacheMissTarget cache query (truncate (labels factors (.leaf level tree side))) :=
        fun answer present => (clean query answer present _ located).2
      rw [stopped_public_nonchain_oracle _ factors.2.1 _ _ _ _ _ _ located
        (by intros; intro h; cases h) localClean]
      simp only [inputHit, outputHit, opened, located, if_false]
    | node level tree =>
      have localClean : CacheMissTarget cache query (truncate (labels factors (.node level tree))) :=
        fun answer present => (clean query answer present _ located).2
      rw [stopped_public_nonchain_oracle _ factors.2.1 _ _ _ _ _ _ located
        (by intros; intro h; cases h) localClean]
      simp only [inputHit, outputHit, opened, located, if_false]

end SigGolfCandidate.Hypertree.SecurityGraphMonitorPublicCoupling

end

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphMonitorProgram
  SecurityGraphMonitorInvariant SecurityGraphMonitorCoupling SecurityGraphMonitorChainState
  SecurityGraphMonitorPublicCoupling SecurityGraphMonitorPublicState SecurityGraphTraceContact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- A normally completed monitored call is an actual supported graph-oracle call,
with exactly the expected cache transition and neither first-contact flag. -/
theorem read_spec (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    ¬inputHit factors exposed query ∧ ¬outputHit factors query result.1 ∧
      result.2.1 = opened factors exposed query ∧
      (result.1, result.2.2) ∈ support
        ((SecurityGraphOracle.publicOracle (privateTable factors) (labels factors) query).run cache) := by
  rw [stopped_public_oracle _ _ _ _ _ initial.1 initial.2.2] at member
  by_cases first : inputHit factors exposed query
  · simp only [if_pos first, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
  · rw [if_neg first, mem_support_bind_iff] at member
    obtain ⟨answer, queried, after⟩ := member
    by_cases second : outputHit factors query answer.1
    · simp only [if_pos second, support_pure, Set.mem_singleton_iff, Option.some_ne_none] at after
    · simp only [if_neg second, stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at after
      subst result
      exact ⟨first, second, rfl, queried⟩

/-- The extraction's wrong-input target equality is exactly the output flag. -/
theorem collision_iff (factors : Factors) (hash : Hash) (query : Query) :
    CollisionContact factors hash query ↔ outputHit factors query (hash query) := by
  unfold CollisionContact outputHit
  cases located : locate query with
  | none => simp
  | some position => simp

/-- An unauthorized canonical predecessor is still hidden by the exposure
invariant, so the extraction's hidden-input contact triggers the input flag. -/
theorem hidden_implies_input (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (safe : ExposedSafe factors.2.2 signed exposed)
    (query : Query) (contact : HiddenContact factors signed query) : inputHit factors exposed query := by
  obtain ⟨address, step, unauthorized, equal⟩ := contact
  have hidden := safe.hidden factors.2.2 signed exposed (predecessor address step) unauthorized
  have canonical : query = (Position.chain address step).input (privateTable factors) (labels factors) := by
    rw [SecurityGraphMonitorCoupling.canonical_chain_input]
    exact equal
  have located := locate_input (privateTable factors) (labels factors) (.chain address step)
  rw [← canonical] at located
  simp only [inputHit, located]
  exact ⟨hidden, canonical⟩

/-- No contact in the actual verifier query-log sense can occur on a normally
completed public-monitor call. This is the deterministic extraction boundary. -/
theorem read_no_contact (factors : Factors) (signed : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (initial : Safe factors signed exposed cache)
    (query : Query) (result : Answer) (hash : Hash) (answer : hash query = result.1)
    (member : some result ∈ support (stopped factors.1 exposed
      (SecurityGraphMonitorOracle.publicStep factors.2.2 exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    ¬Contact factors signed hash query := by
  have spec := read_spec factors signed exposed cache initial query result member
  intro contact
  rcases contact with collision | hidden
  · have hit := (collision_iff factors hash query).mp collision
    rw [answer] at hit
    exact spec.2.1 hit
  · exact spec.1 (hidden_implies_input factors signed exposed initial.2.1 query hidden)

end SigGolfCandidate.Hypertree.SecurityGraphMonitorNoContact
