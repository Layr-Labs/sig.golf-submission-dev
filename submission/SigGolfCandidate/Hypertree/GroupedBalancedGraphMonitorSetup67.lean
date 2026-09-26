import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompileCoupling67

/-! First disclose only tree-node labels. These public values determine every
canonical WOTS message and hence the initial safe frontier; no hidden chain
point is consulted while choosing the second disclosure list. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorAuthorization67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open scoped Classical

def IsNode : Point → Prop
  | .inl position => position.val.tag.val = 4
  | _ => False

noncomputable def metadataPoints : List Point :=
  (Finset.univ.filter IsNode).toList

@[simp] theorem mem_metadataPoints (point : Point) :
    point ∈ metadataPoints ↔ IsNode point := by
  simp [metadataPoints]

theorem node_metadata (position : Position)
    (node : position.val.tag.val = 4) :
    (.inl position : Point) ∈ metadataPoints := by
  simp [IsNode, node]

noncomputable def metadataCache (table : PointTable) : QueryCache PointSpec :=
  revealCache table metadataPoints ∅

theorem metadata_lookup (table : PointTable) (position : Position)
    (node : position.val.tag.val = 4) :
    metadataCache table (.inl position) = some (table (.inl position)) :=
  GroupedBalancedGraphMonitorRequired67.revealCache_mem
    table metadataPoints ∅ (.inl position) (node_metadata position node)

def metadataLabels (cache : QueryCache PointSpec) :
    GroupedBalancedSecurityGraph67.Labels :=
  GroupedBalancedGraphMonitorTable67.labelsOf (knownTable cache)

theorem canonical_metadata (table : PointTable)
    (base : Fin 150) (leaf : BitVec 160) :
    canonicalMessage (metadataLabels (metadataCache table)) base leaf =
      canonicalMessage (GroupedBalancedGraphMonitorTable67.labelsOf table) base leaf := by
  unfold canonicalMessage
  split_ifs with zero
  · have known := metadata_lookup table
      (bottomNode ⟨9, by decide⟩ leaf) rfl
    simpa only [metadataLabels, knownTable,
      GroupedBalancedGraphMonitorTable67.labelsOf, Option.getD_some] using
      congrArg (fun value : Option (BitVec 256) => truncate (value.getD 0)) known
  · have known := metadata_lookup table
      (upperNode ⟨base.val - 1, by omega⟩ leaf) rfl
    simpa only [metadataLabels, knownTable,
      GroupedBalancedGraphMonitorTable67.labelsOf, Option.getD_some] using
      congrArg (fun value : Option (BitVec 256) => truncate (value.getD 0)) known

theorem threshold_metadata (table : PointTable)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    threshold (metadataLabels (metadataCache table)) base leaf chain =
      threshold (GroupedBalancedGraphMonitorTable67.labelsOf table) base leaf chain := by
  unfold threshold
  rw [canonical_metadata]

theorem authorized_metadata_iff (table : PointTable) (point : Point) :
    Authorized (metadataLabels (metadataCache table)) ∅ point ↔
      Authorized (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ point := by
  cases point with
  | inl position =>
      simp only [Authorized]
      constructor <;> intro authorization base leaf chain step same
      · rw [← threshold_metadata]
        exact authorization base leaf chain step same
      · rw [threshold_metadata]
        exact authorization base leaf chain step same
  | inr rest =>
      cases rest with
      | inl index => rfl
      | inr address =>
          rcases address with ⟨addressKey, chain⟩
          rcases addressKey with ⟨base, leaf⟩
          simp only [Authorized, threshold_metadata]

noncomputable def frontier (labels : GroupedBalancedSecurityGraph67.Labels) :
    List Point :=
  (Finset.univ.filter (Authorized labels ∅)).toList

@[simp] theorem mem_frontier (labels : GroupedBalancedSecurityGraph67.Labels)
    (point : Point) :
    point ∈ frontier labels ↔ Authorized labels ∅ point := by
  simp [frontier]

theorem frontier_metadata (table : PointTable) :
    frontier (metadataLabels (metadataCache table)) =
      frontier (GroupedBalancedGraphMonitorTable67.labelsOf table) := by
  unfold frontier
  have same : (Finset.univ.filter
      (Authorized (metadataLabels (metadataCache table)) ∅) : Finset Point) =
      Finset.univ.filter
        (Authorized (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅) := by
    ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact authorized_metadata_iff table point
  exact congrArg (fun set : Finset Point => set.toList) same

noncomputable def cache (table : PointTable) : QueryCache PointSpec :=
  revealCache table
    (frontier (GroupedBalancedGraphMonitorTable67.labelsOf table))
    (metadataCache table)

noncomputable def setup {α : Type}
    (next : QueryCache PointSpec → Program α) : Program α :=
  disclose metadataPoints ∅ (fun known =>
    disclose (frontier (metadataLabels known)) known next)

theorem run_disclose {α : Type} (table : PointTable)
    (points : List Point) (exposed : QueryCache PointSpec)
    (next : QueryCache PointSpec → Program α) :
    run table exposed (disclose points exposed next) =
      run table (revealCache table points exposed)
        (next (revealCache table points exposed)) := by
  induction points generalizing exposed with
  | nil => rfl
  | cons point rest ih =>
      simp only [disclose, run, revealCache]
      exact ih _

theorem run_setup {α : Type} (table : PointTable)
    (next : QueryCache PointSpec → Program α) :
    run table ∅ (setup next) = run table (cache table) (next (cache table)) := by
  rw [setup, run_disclose, run_disclose]
  simp only [metadataCache, ← frontier_metadata, cache]

theorem stopped_setup {α : Type} (table : PointTable)
    (next : QueryCache PointSpec → Program α) :
    GroupedBalancedGraphMonitorStop67.stopped table ∅ (setup next) =
      GroupedBalancedGraphMonitorStop67.stopped table
        (cache table) (next (cache table)) := by
  rw [setup, GroupedBalancedGraphMonitorResidual67.stopped_disclose,
    GroupedBalancedGraphMonitorResidual67.stopped_disclose]
  simp only [metadataCache, ← frontier_metadata, cache]

theorem node_authorized (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (position : Position) (node : position.val.tag.val = 4) :
    Authorized labels signedBottom (.inl position) := by
  intro base leaf chain step same
  have tags := congrArg (fun point : Position => point.val.tag.val) same
  change position.val.tag.val = 2 at tags
  omega

theorem metadata_safe (table : PointTable) :
    ExposedSafe (GroupedBalancedGraphMonitorTable67.labelsOf table)
      ∅ (metadataCache table) := by
  apply ExposedSafe.revealCache _ _ table metadataPoints ∅
    (exposedSafe_empty _ _)
  intro point member
  cases point with
  | inl position =>
      exact node_authorized _ ∅ position
        ((mem_metadataPoints _).mp member)
  | inr rest =>
      cases rest <;> cases (mem_metadataPoints _).mp member

theorem cache_safe (table : PointTable) :
    Safe table ∅ (cache table) ∅ := by
  let labels := GroupedBalancedGraphMonitorTable67.labelsOf table
  have agreeEmpty : GroupedBalancedGraphMonitorResidual67.Agree table ∅ := by
    intro point value present
    cases present
  have firstAgree := GroupedBalancedGraphMonitorResidual67.agree_revealCache
    table metadataPoints ∅ agreeEmpty
  have fullAgree := GroupedBalancedGraphMonitorResidual67.agree_revealCache
    table (frontier labels) (metadataCache table) firstAgree
  have fullSafe := ExposedSafe.revealCache labels ∅ table
    (frontier labels) (metadataCache table) (metadata_safe table)
    (fun point member => (mem_frontier labels point).mp member)
  exact ⟨fullAgree, fullSafe, residualSafe_empty table⟩

theorem revealCache_outside (table : PointTable) (points : List Point)
    (initial : QueryCache PointSpec) (point : Point)
    (absent : point ∉ points) :
    revealCache table points initial point = initial point := by
  induction points generalizing initial with
  | nil => rfl
  | cons other rest ih =>
      have different : point ≠ other := fun equal =>
        absent (List.mem_cons.mpr (Or.inl equal))
      have later : point ∉ rest := fun member =>
        absent (List.mem_cons_of_mem _ member)
      rw [revealCache, ih _ later, QueryCache.cacheQuery_of_ne _ _ different]

theorem cache_lookup (table : PointTable) (point : Point) :
    cache table point =
      if Authorized (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ point
      then some (table point) else none := by
  let labels := GroupedBalancedGraphMonitorTable67.labelsOf table
  by_cases allowed : Authorized labels ∅ point
  · rw [if_pos allowed]
    exact GroupedBalancedGraphMonitorRequired67.revealCache_mem table
      (frontier labels) (metadataCache table) point
      ((mem_frontier labels point).mpr allowed)
  · rw [if_neg allowed]
    have absentFrontier : point ∉ frontier labels :=
      fun member => allowed ((mem_frontier labels point).mp member)
    have absentMetadata : point ∉ metadataPoints := by
      intro member
      cases point with
      | inl position =>
          exact allowed (node_authorized labels ∅ position
            ((mem_metadataPoints _).mp member))
      | inr rest =>
          cases rest <;> cases (mem_metadataPoints _).mp member
    rw [cache, revealCache_outside table (frontier labels)
      (metadataCache table) point absentFrontier,
      metadataCache,
      revealCache_outside table metadataPoints ∅ point absentMetadata]
    rfl

theorem cache_covers (table : PointTable) (point : Point)
    (allowed : Authorized (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ point) :
    cache table point = some (table point) := by
  rw [cache_lookup, if_pos allowed]

theorem cache_hidden (table : PointTable) (point : Point)
    (hidden : ¬Authorized (GroupedBalancedGraphMonitorTable67.labelsOf table) ∅ point) :
    cache table point = none := by
  rw [cache_lookup, if_neg hidden]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67
