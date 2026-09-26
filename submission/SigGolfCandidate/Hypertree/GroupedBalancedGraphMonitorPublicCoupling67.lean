import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicState67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSuccessor67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainSafe67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicCoupling67. -/
section
/-! A normally completed chain query preserves authorization and residual
cache separation; a hidden canonical predecessor stops as a contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainSafe67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorResidual67 GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorPublicState67 GroupedBalancedGraphMonitorCoupling67
open GroupedBalancedGraphMonitorSuccessor67 GroupedBalancedGraphMonitorPredecessor67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

theorem graphInput_chain (table : PointTable) (position : Position)
    (tagTwo : position.val.tag.val = 2) :
    GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position =
    (match predecessor position.val with
      | none => position.input []
      | some previous => position.input (bytes (truncate (table previous)))) := by
  unfold GroupedBalancedGraphCausality67.graphInput
  rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo,
    GroupedBalancedGraphMonitorPredecessor67.chain_payload_eq]
  cases predecessor position.val <;> rfl

theorem chain_read_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (position : Position) (query : Query)
    (tagTwo : position.val.tag.val = 2)
    (located : GroupedBalancedGraphQuery67.locate query = some position)
    (result : Answer)
    (member : some result ∈ support (stopped table exposed
      (chainStep exposed cache position query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe table signedBottom result.2.1 result.2.2 ∧
      (query = GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position →
        ∀ previous, predecessor position.val = some previous →
          GroupedBalancedGraphMonitorAuthorization67.Authorized
            (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom previous) ∧
      (query ≠ GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position →
        truncate result.1 ≠ truncate (table (.inl position))) := by
  have clean := initial.2.2.target table cache query position located
  rw [stopped_chain table exposed cache position query _ tagTwo initial.1 clean] at member
  have graphInputEq := graphInput_chain table position tagTwo
  unfold chainStopped at member
  cases previous : predecessor position.val with
  | none =>
      rw [previous] at graphInputEq
      by_cases canonical : query = position.input []
      · simp only [previous, if_pos canonical, Bool.false_eq_true,
          ↓reduceIte, stopped, support_pure,
          Set.mem_singleton_iff, Option.some.injEq] at member
        subst result
        have authorized := authorized_no_predecessor
          (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom position previous
        have safe : Safe table signedBottom
            (exposed.cacheQuery (.inl position) (table (.inl position))) cache :=
          ⟨initial.1.cacheQuery table exposed (.inl position),
            initial.2.1.cacheQuery _ _ _ _ _ authorized,
            initial.2.2⟩
        refine ⟨safe, ?_, ?_⟩
        · intro _ point impossible
          cases impossible
        · intro different
          exact False.elim (different (canonical.trans graphInputEq.symm))
      · have different : query ≠ GroupedBalancedGraphCausality67.graphInput
            (GroupedBalancedGraphMonitorTable67.privateOf table)
            (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
          rw [graphInputEq]
          exact canonical
        simp only [previous, if_neg canonical] at member
        have safe := residual_read_safe table signedBottom exposed cache initial
          query position located different result member
        refine ⟨safe.1, ?_, ?_⟩
        · intro _ point impossible
          cases impossible
        · intro _
          exact safe.2
  | some predecessorPoint =>
      rw [previous] at graphInputEq
      by_cases canonical : query = position.input
          (bytes (truncate (table predecessorPoint)))
      · cases known : exposed predecessorPoint with
        | none =>
            simp only [previous, if_pos canonical, known, if_true,
              support_pure, Set.mem_singleton_iff,
              Option.some_ne_none] at member
        | some value =>
            simp only [previous, if_pos canonical, known,
              Option.some_ne_none, if_false, stopped,
              support_pure, Set.mem_singleton_iff,
              Option.some.injEq] at member
            subst result
            have predecessorAuth := initial.2.1 predecessorPoint value known
            have targetAuth := authorized_after_predecessor
              (GroupedBalancedGraphMonitorTable67.labelsOf table) signedBottom
              position predecessorPoint previous predecessorAuth
            have safe : Safe table signedBottom
                (exposed.cacheQuery (.inl position) (table (.inl position))) cache :=
              ⟨initial.1.cacheQuery table exposed (.inl position),
                initial.2.1.cacheQuery _ _ _ _ _ targetAuth,
                initial.2.2⟩
            refine ⟨safe, ?_, ?_⟩
            · intro _ point found
              have same := Option.some.inj found
              subst point
              exact predecessorAuth
            · intro different
              exact False.elim (different (canonical.trans graphInputEq.symm))
      · have different : query ≠ GroupedBalancedGraphCausality67.graphInput
            (GroupedBalancedGraphMonitorTable67.privateOf table)
            (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
          rw [graphInputEq]
          exact canonical
        simp only [previous, if_neg canonical] at member
        have safe := residual_read_safe table signedBottom exposed cache initial
          query position located different result member
        exact ⟨safe.1, fun same => False.elim (different same),
          fun _ => safe.2⟩

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainSafe67
end

/-! One contact-free public query preserves all grouped monitor invariants. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicUnified67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67 GroupedBalancedGraphMonitorPublicState67
open GroupedBalancedGraphMonitorChainSafe67
set_option backward.isDefEq.respectTransparency false

theorem public_read_safe (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped table exposed
      (publicStep exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    Safe table signedBottom result.2.1 result.2.2 := by
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      exact outside_read_safe table signedBottom exposed cache initial
        query located result member
  | some position =>
      by_cases tagTwo : position.val.tag.val = 2
      · have dispatch : publicStep exposed cache query
            (fun answer opened residual =>
              GroupedBalancedGraphMonitorProgram67.Program.done (answer, opened, residual)) =
            chainStep exposed cache position query
              (fun answer opened residual =>
                GroupedBalancedGraphMonitorProgram67.Program.done (answer, opened, residual)) := by
          simp only [publicStep, located, if_pos tagTwo]
        rw [dispatch] at member
        exact (chain_read_safe table signedBottom exposed cache initial
          position query tagTwo located result member).1
      · exact (nonchain_read_safe table signedBottom exposed cache initial
          position query located tagTwo result member).1

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicUnified67


/-! Identical-until-contact coupling of one grouped public hash query to the
explicit planted graph oracle, with both caches and its output retained. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicCoupling67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorResidual67 GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorMetadata67 GroupedBalancedGraphMonitorCoupling67
open GroupedBalancedGraphMonitorChainSafe67 GroupedBalancedGraphMonitorPredecessor67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

def inputHit (table : PointTable) (exposed : QueryCache PointSpec)
    (query : Query) : Prop :=
  match GroupedBalancedGraphQuery67.locate query with
  | none => False
  | some position =>
      if position.val.tag.val = 2 then
        match predecessor position.val with
        | none => False
        | some previous => exposed previous = none ∧
            query = GroupedBalancedGraphCausality67.graphInput
              (GroupedBalancedGraphMonitorTable67.privateOf table)
              (GroupedBalancedGraphMonitorTable67.labelsOf table) position
      else False

def outputHit (table : PointTable) (query : Query)
    (answer : BitVec 256) : Prop :=
  match GroupedBalancedGraphQuery67.locate query with
  | none => False
  | some position =>
      query ≠ GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position ∧
      truncate answer = truncate (table (.inl position))

noncomputable def opened (table : PointTable)
    (exposed : QueryCache PointSpec) (query : Query) : QueryCache PointSpec :=
  match GroupedBalancedGraphQuery67.locate query with
  | none => exposed
  | some position =>
      let metadata := if position.val.tag.val = 2 then exposed
        else revealCache table (required position) exposed
      if query = GroupedBalancedGraphCausality67.graphInput
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) position then
        metadata.cacheQuery (.inl position) (table (.inl position))
      else metadata

theorem stopped_public_oracle {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α)
    (agree : Agree table exposed) (clean : ResidualSafe table cache) :
    stopped table exposed (publicStep exposed cache query next) =
      (if inputHit table exposed query then (pure none : ProbComp (Option α)) else
        (GroupedBalancedGraphOracle67.publicOracle
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache >>= fun result =>
        if outputHit table query result.1 then (pure none : ProbComp (Option α))
        else stopped table (opened table exposed query)
          (next result.1 (opened table exposed query) result.2)) := by
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [inputHit, outputHit, opened, located, if_false]
      rw [GroupedBalancedGraphMonitorResidual67.stopped_outside table exposed cache query next located]
      simp only [GroupedBalancedGraphOracle67.publicOracle, GroupedBalancedGraphOracle67.canonical, located]
  | some position =>
      have localClean := clean.target table cache query position located
      by_cases tagTwo : position.val.tag.val = 2
      · have dispatch : publicStep exposed cache query next =
            chainStep exposed cache position query next := by
          simp only [publicStep, located, if_pos tagTwo]
        rw [dispatch, stopped_chain table exposed cache position query next
          tagTwo agree localClean]
        have graphInputEq := graphInput_chain table position tagTwo
        unfold chainStopped
        simp only [inputHit, outputHit, opened,
          GroupedBalancedGraphOracle67.publicOracle,
          GroupedBalancedGraphOracle67.canonical, located, if_pos tagTwo]
        cases previous : predecessor position.val with
        | none =>
            rw [previous] at graphInputEq
            simp only [previous, false_and, if_false]
            by_cases canonical : query = position.input []
            · simp [graphInputEq, canonical]
              rfl
            · simp [graphInputEq, canonical]
        | some predecessorPoint =>
            rw [previous] at graphInputEq
            simp only [previous]
            by_cases canonical : query = position.input
                (bytes (truncate (table predecessorPoint)))
            · by_cases hidden : exposed predecessorPoint = none
              · simp [graphInputEq, canonical, hidden]
              · simp [graphInputEq, canonical, hidden]
                rfl
            · simp [graphInputEq, canonical]
      · rw [stopped_public_nonchain table exposed cache position query next
          located tagTwo agree localClean]
        simp only [inputHit, outputHit, opened,
          GroupedBalancedGraphOracle67.publicOracle,
          GroupedBalancedGraphOracle67.canonical, located, if_neg tagTwo]
        by_cases canonical : query = GroupedBalancedGraphCausality67.graphInput
            (GroupedBalancedGraphMonitorTable67.privateOf table)
            (GroupedBalancedGraphMonitorTable67.labelsOf table) position
        · simp [canonical]
          rfl
        · simp [canonical]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicCoupling67
