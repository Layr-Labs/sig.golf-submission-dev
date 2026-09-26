import SigGolfCandidate.Hypertree.GroupedBalancedGraphSignHistory67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67

/-! Honest signer disclosures extend the bottom-index authorization set.
Every upper WOTS point was already in the initial metadata-defined frontier. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSignExposure67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorOracle67
open GroupedBalancedGraphSignHistory67
open scoped Classical

theorem authorized_mono (labels : Labels)
    {first second : Finset (BitVec 160)} (subset : first ⊆ second)
    {point : Point} (allowed : Authorized labels first point) :
    Authorized labels second point := by
  cases point with
  | inl position => exact allowed
  | inr privatePoint =>
      cases privatePoint with
      | inl index => exact subset allowed
      | inr source => exact allowed

theorem safe_mono (table : PointTable)
    {first second : Finset (BitVec 160)} (subset : first ⊆ second)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (safe : Safe table first exposed cache) :
    Safe table second exposed cache := by
  exact ⟨safe.1, fun point value known =>
    authorized_mono _ subset (safe.2.1 point value known), safe.2.2⟩

theorem safe_reveal_bottom (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (safe : Safe table signedBottom exposed cache)
    (index : BitVec 160) :
    Safe table (insert index signedBottom)
      (exposed.cacheQuery (.inr (.inl index)) (table (.inr (.inl index)))) cache := by
  have enlarged := safe_mono table (Finset.subset_insert index signedBottom)
    exposed cache safe
  refine ⟨GroupedBalancedGraphMonitorResidual67.Agree.cacheQuery table exposed
      enlarged.1 (.inr (.inl index)), ?_, enlarged.2.2⟩
  exact GroupedBalancedGraphMonitorInvariant67.ExposedSafe.cacheQuery
    (GroupedBalancedGraphMonitorTable67.labelsOf table)
    (insert index signedBottom) exposed enlarged.2.1
    (.inr (.inl index)) (table (.inr (.inl index)))
    (Finset.mem_insert_self index signedBottom)

theorem canonical_head_cached (table : PointTable)
    (labels : Labels)
    (sameLabels : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (height : Nat) (rest : List Nat) (base index : Nat)
    (head : GroupedBalancedUpperTree67.Witness height)
    (tail : GroupedBalancedScheme67.UpperWitnesses rest)
    (canonical : CanonicalWitnesses labels table (height :: rest) base index
      (.cons head tail))
    (chain : Fin 67) :
    ∃ baseFin : Fin 150, baseFin.val + 10 = base ∧
      let point := earlierPoint baseFin (BitVec.ofNat 160 index) chain
        (GroupedBalancedUpperTree67.digit
          (canonicalMessage labels baseFin (BitVec.ofNat 160 index)) chain)
      GroupedBalancedUpperIndex67.witnessValues head chain =
        truncate (table point) ∧
      GroupedBalancedGraphMonitorSetup67.cache table point = some (table point) := by
  obtain ⟨baseFin, baseEq, values⟩ := canonical.1
  refine ⟨baseFin, baseEq, values chain, ?_⟩
  apply GroupedBalancedGraphMonitorSetup67.cache_covers
  rw [← sameLabels]
  exact canonical_signature_point_authorized labels ∅ baseFin
    (BitVec.ofNat 160 index) chain

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSignExposure67
