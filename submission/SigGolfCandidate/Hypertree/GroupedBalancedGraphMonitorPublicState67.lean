import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCoupling67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorAuthorization67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSafeReveal67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorMetadata67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorInvariant67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicState67. -/
section
/-! Cache invariants for an identical-until-contact simulation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorInvariant67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67 GroupedBalancedGraphMonitorOracle67
open GroupedBalancedGraphMonitorResidual67
set_option backward.isDefEq.respectTransparency false
open scoped Classical

def ResidualSafe (table : PointTable) (cache : QueryCache HashSpec) : Prop :=
  ∀ query answer, cache query = some answer →
    ∀ position, GroupedBalancedGraphQuery67.locate query = some position →
      query ≠ GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position ∧
      truncate answer ≠ truncate (table (.inl position))

@[simp] theorem residualSafe_empty (table : PointTable) :
    ResidualSafe table ∅ := by
  intro query answer present
  cases present

theorem ResidualSafe.cacheQuery (table : PointTable)
    (cache : QueryCache HashSpec) (safe : ResidualSafe table cache)
    (query : Query) (answer : BitVec 256)
    (clean : ∀ position, GroupedBalancedGraphQuery67.locate query = some position →
      query ≠ GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position ∧
      truncate answer ≠ truncate (table (.inl position))) :
    ResidualSafe table (cache.cacheQuery query answer) := by
  intro other value present position located
  by_cases same : other = query
  · subst other
    have values : answer = value := Option.some.inj
      (by simpa only [QueryCache.cacheQuery_self] using present)
    subst value
    exact clean position located
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other value present position located

theorem ResidualSafe.target (table : PointTable)
    (cache : QueryCache HashSpec) (safe : ResidualSafe table cache)
    (query : Query) (position : Position)
    (located : GroupedBalancedGraphQuery67.locate query = some position) :
    CacheMissTarget cache query (truncate (table (.inl position))) := by
  intro answer present
  exact (safe query answer present position located).2

def ExposedSafe (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (cache : QueryCache PointSpec) : Prop :=
  ∀ point value, cache point = some value →
    Authorized labels signedBottom point

@[simp] theorem exposedSafe_empty (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) :
    ExposedSafe labels signedBottom ∅ := by
  intro point value present
  cases present

theorem ExposedSafe.cacheQuery (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (cache : QueryCache PointSpec) (safe : ExposedSafe labels signedBottom cache)
    (point : Point) (value : BitVec 256)
    (authorized : Authorized labels signedBottom point) :
    ExposedSafe labels signedBottom (cache.cacheQuery point value) := by
  intro other answer present
  by_cases same : other = point
  · subst other
    exact authorized
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other answer present

theorem ExposedSafe.hidden (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (cache : QueryCache PointSpec)
    (safe : ExposedSafe labels signedBottom cache)
    (point : Point) (unauthorized : ¬Authorized labels signedBottom point) :
    cache point = none := by
  cases present : cache point with
  | none => rfl
  | some value => exact False.elim (unauthorized (safe point value present))

theorem ExposedSafe.revealCache (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (table : PointTable) (points : List Point)
    (cache : QueryCache PointSpec)
    (safe : ExposedSafe labels signedBottom cache)
    (authorized : ∀ point ∈ points, Authorized labels signedBottom point) :
    ExposedSafe labels signedBottom (revealCache table points cache) := by
  induction points generalizing cache with
  | nil => exact safe
  | cons point points ih =>
      exact ih (cache.cacheQuery point (table point))
        (safe.cacheQuery labels signedBottom cache point (table point)
          (authorized point (by simp)))
        (fun other member => authorized other (by simp [member]))

def Safe (table : PointTable) (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) : Prop :=
  Agree table exposed ∧
  ExposedSafe (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom exposed ∧
  ResidualSafe table cache

@[simp] theorem safe_empty (table : PointTable)
    (signedBottom : Finset (BitVec 160)) :
    Safe table signedBottom ∅ ∅ := by
  refine ⟨?_, exposedSafe_empty _ _, residualSafe_empty _⟩
  intro point answer present
  cases present

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorInvariant67

end

/-! Contact-free metadata and residual queries preserve the monitor caches. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicState67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorResidual67 GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorMetadata67 GroupedBalancedGraphMonitorSafeReveal67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

abbrev Answer := BitVec 256 × QueryCache PointSpec × QueryCache HashSpec

theorem metadata_state_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (position : Position) :
    Safe table signedBottom
      (revealCache table (required position) exposed) cache := by
  refine ⟨agree_revealCache table (required position) exposed initial.1,
    ?_, initial.2.2⟩
  exact initial.2.1.revealCache _ _ table (required position) exposed
    (fun point member => required_authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom position point member)

theorem residual_read_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (query : Query) (position : Position)
    (located : GroupedBalancedGraphQuery67.locate query = some position)
    (different : query ≠ GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position)
    (result : Answer)
    (member : some result ∈ support (do
      let output ← (randomOracle (spec := HashSpec) query).run cache
      if truncate output.1 = truncate (table (.inl position)) then pure none
      else pure (some (output.1, exposed, output.2)))) :
    Safe table signedBottom result.2.1 result.2.2 ∧
      truncate result.1 ≠ truncate (table (.inl position)) := by
  cases present : cache query with
  | some answer =>
      have miss := (initial.2.2 query answer present position located).2
      simp only [randomOracle.run_eq, present, pure_bind, if_neg miss,
        support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact ⟨initial, miss⟩
  | none =>
      simp only [randomOracle.run_eq, present, bind_assoc, pure_bind,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      by_cases hit : truncate answer = truncate (table (.inl position))
      · simp only [if_pos hit, support_pure, Set.mem_singleton_iff,
          Option.some_ne_none] at member
      · simp only [if_neg hit, support_pure, Set.mem_singleton_iff,
          Option.some.injEq] at member
        subst result
        have residualSafe : ResidualSafe table (cache.cacheQuery query answer) := by
          apply initial.2.2.cacheQuery table cache query answer
          intro other otherLocated
          have same : position = other :=
            Option.some.inj (located.symm.trans otherLocated)
          subst other
          exact ⟨different, hit⟩
        exact ⟨⟨initial.1, initial.2.1, residualSafe⟩, hit⟩

theorem nonchain_read_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (position : Position) (query : Query)
    (located : GroupedBalancedGraphQuery67.locate query = some position)
    (nonchain : position.val.tag.val ≠ 2)
    (result : Answer)
    (member : some result ∈ support (stopped table exposed
      (publicStep exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe table signedBottom result.2.1 result.2.2 ∧
      (query ≠ GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position →
        truncate result.1 ≠ truncate (table (.inl position))) := by
  have clean : CacheMissTarget cache query (truncate (table (.inl position))) :=
    initial.2.2.target table cache query position located
  rw [stopped_public_nonchain table exposed cache position query _
    located nonchain initial.1 clean] at member
  let opened := revealCache table (required position) exposed
  have openedSafe := metadata_state_safe table signedBottom exposed cache initial position
  by_cases canonical : query = GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position
  · simp only [if_pos canonical, stopped, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at member
    subst result
    have authorized : GroupedBalancedGraphMonitorAuthorization67.Authorized
        (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom (.inl position) :=
      safe_public _ _ position (Or.inl nonchain)
    exact ⟨⟨openedSafe.1.cacheQuery _ _ (.inl position),
      openedSafe.2.1.cacheQuery _ _ _ _ _ authorized,
      openedSafe.2.2⟩, fun different => False.elim (different canonical)⟩
  · rw [if_neg canonical] at member
    have safe := residual_read_safe table signedBottom _ cache openedSafe
      query position located canonical result member
    exact ⟨safe.1, fun _ => safe.2⟩

theorem outside_read_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (query : Query) (located : GroupedBalancedGraphQuery67.locate query = none)
    (result : Answer)
    (member : some result ∈ support (stopped table exposed
      (publicStep exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe table signedBottom result.2.1 result.2.2 := by
  rw [stopped_outside table exposed cache query _ located] at member
  cases present : cache query with
  | some answer =>
      simp only [randomOracle.run_eq, present, pure_bind, stopped,
        support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact initial
  | none =>
      simp only [randomOracle.run_eq, present, bind_assoc, pure_bind,
        stopped, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at member
      obtain ⟨answer, _, same⟩ := member
      subst result
      refine ⟨initial.1, initial.2.1,
        initial.2.2.cacheQuery table cache query answer ?_⟩
      intro position impossible
      rw [located] at impossible
      cases impossible

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicState67
