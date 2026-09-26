import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorResidual67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOracle67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorRequired67

/-! Exact local stopped semantics for public leaf and Merkle-node queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorMetadata67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorResidual67
set_option backward.isDefEq.respectTransparency false

theorem stopped_public_nonchain {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α)
    (located : GroupedBalancedGraphQuery67.locate query = some position)
    (nonchain : position.val.tag.val ≠ 2)
    (agree : Agree table exposed)
    (clean : CacheMissTarget residual query (truncate (table (.inl position)))) :
    stopped table exposed (publicStep exposed residual query next) = (
      let opened := revealCache table (required position) exposed;
      if query = GroupedBalancedGraphCausality67.graphInput
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) position then
        stopped table
          (opened.cacheQuery (.inl position) (table (.inl position)))
          (next (table (.inl position))
            (opened.cacheQuery (.inl position) (table (.inl position))) residual)
      else do
        let result ← (randomOracle (spec := HashSpec) query).run residual
        if truncate result.1 = truncate (table (.inl position)) then pure none
        else stopped table opened (next result.1 opened result.2)) := by
  have openedAgree := agree_revealCache table (required position) exposed agree
  have payloadEq := GroupedBalancedGraphMonitorRequired67.required_after_reveal
    table exposed position nonchain
  simp only [publicStep, located, if_neg nonchain]
  rw [stopped_disclose]
  change stopped table (revealCache table (required position) exposed)
    (if query = position.input _ then _ else _) = _
  rw [payloadEq]
  change stopped table (revealCache table (required position) exposed)
    (if query = GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position then _ else _) = _
  by_cases matched : query = GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position
  · simp only [if_pos matched, stopped]
  · simp only [if_neg matched]
    exact stopped_residualStep table
      (revealCache table (required position) exposed) residual query
      (.inl position) next openedAgree clean

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorMetadata67
