import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67

/-! A public graph-oracle call changes the residual hash cache only at its
queried input. This keeps tag-5 cache coordinates isolated in the audit. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphPublicResidualFrame67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorOracle67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def Frame (residual : QueryCache HashSpec) (query : Query)
    (result : Outcome (BitVec 256 × QueryCache PointSpec ×
      QueryCache HashSpec)) : Prop :=
  result.value.2.2 = residual ∨
    ∃ answer, result.value.2.2 = residual.cacheQuery query answer

theorem frame_done (residual : QueryCache HashSpec) (query : Query)
    (answer : BitVec 256) (exposed : QueryCache PointSpec) :
    Frame residual query ⟨(answer, exposed, residual), false, 0⟩ :=
  Or.inl rfl

theorem frame_done_cached (residual : QueryCache HashSpec) (query : Query)
    (answer : BitVec 256) (exposed : QueryCache PointSpec) :
    Frame residual query
      ⟨(answer, exposed, residual.cacheQuery query answer), false, 0⟩ :=
  Or.inr ⟨answer, rfl⟩

theorem residualStep_frame (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) (target : Point) :
    ∀ result ∈ support (run table exposed
      (residualStep exposed residual query target
        (fun answer opened updated => .done (answer, opened, updated)))),
      Frame residual query result := by
  intro result member
  cases cached : residual query with
  | some answer =>
      simp only [residualStep, cached, run, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      exact frame_done residual query answer exposed
  | none =>
      cases known : exposed target with
      | some digest =>
          simp only [residualStep, cached, known, run,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, member⟩ := member
          simp only [support_map, Set.mem_image, run, support_pure,
            Set.mem_singleton_iff] at member
          obtain ⟨child, childMember, same⟩ := member
          subst child
          subst result
          exact Or.inr ⟨answer, rfl⟩
      | none =>
          simp only [residualStep, cached, known, run,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, member⟩ := member
          simp only [support_map, Set.mem_image, run, support_pure,
            Set.mem_singleton_iff] at member
          obtain ⟨child, childMember, same⟩ := member
          subst child
          subst result
          exact Or.inr ⟨answer, rfl⟩

theorem frame_addTest (residual : QueryCache HashSpec)
    (query : Query) (hit : Bool)
    (result : Outcome (BitVec 256 × QueryCache PointSpec ×
      QueryCache HashSpec)) :
    Frame residual query (addTest hit result) ↔
      Frame residual query result := Iff.rfl

theorem chainStep_frame (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : GroupedBalancedSecurityGraph67.Position)
    (query : Query) :
    ∀ result ∈ support (run table exposed
      (chainStep exposed residual position query
        (fun answer opened updated => .done (answer, opened, updated)))),
      Frame residual query result := by
  intro result member
  cases previous : GroupedBalancedGraphMonitorPredecessor67.predecessor
      position.val with
  | none =>
      by_cases exact : query = position.input []
      · simp only [chainStep, previous, exact, if_true, run,
          support_pure, Set.mem_singleton_iff] at member
        subst result
        exact Or.inl rfl
      · have converted : result ∈ support (run table exposed
            (residualStep exposed residual query (.inl position)
              (fun answer opened updated => .done (answer, opened, updated)))) := by
          simpa only [chainStep, previous, exact, if_false] using member
        exact residualStep_frame table exposed residual query (.inl position)
          result converted
  | some earlier =>
      cases parsed : parsedChainPayload position query with
      | none =>
          have converted : result ∈ support (run table exposed
              (residualStep exposed residual query (.inl position)
                (fun answer opened updated => .done (answer, opened, updated)))) := by
            simpa only [chainStep, previous, parsed] using member
          exact residualStep_frame table exposed residual query (.inl position)
            result converted
      | some point =>
          cases known : exposed earlier with
          | none =>
              simp only [chainStep, previous, parsed, known, run,
                support_map, Set.mem_image] at member
              obtain ⟨child, childMember, same⟩ := member
              subst result
              exact (frame_addTest residual query _ child).2
                (residualStep_frame table exposed residual query (.inl position)
                  child childMember)
          | some digest =>
              by_cases equal : point = truncate digest
              · simp only [chainStep, previous, parsed, known, equal,
                  if_true, run, support_pure, Set.mem_singleton_iff] at member
                subst result
                exact Or.inl rfl
              · have converted : result ∈ support (run table exposed
                    (residualStep exposed residual query (.inl position)
                      (fun answer opened updated =>
                        .done (answer, opened, updated)))) := by
                  simpa only [chainStep, previous, parsed, known,
                    equal, if_false] using member
                exact residualStep_frame table exposed residual query
                  (.inl position) result converted

theorem publicStep_frame (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) :
    ∀ result ∈ support (run table exposed
      (publicStep exposed residual query
        (fun answer opened updated => .done (answer, opened, updated)))),
      Frame residual query result := by
  intro result member
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      cases cached : residual query with
      | some answer =>
          simp only [publicStep, located, cached, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact Or.inl rfl
      | none =>
          simp only [publicStep, located, cached, run,
            mem_support_bind_iff] at member
          obtain ⟨answer, _, child⟩ := member
          simp only [run, support_pure, Set.mem_singleton_iff] at child
          subst result
          exact Or.inr ⟨answer, rfl⟩
  | some position =>
      by_cases chain : position.val.tag.val = 2
      · have converted : result ∈ support (run table exposed
            (chainStep exposed residual position query
              (fun answer opened updated => .done (answer, opened, updated)))) := by
          simpa only [publicStep, located, chain, if_true] using member
        exact chainStep_frame table exposed residual position query
          result converted
      · have disclosed :
            run table exposed
              (publicStep exposed residual query
                (fun answer opened updated => .done (answer, opened, updated))) =
              run table
                (revealCache table (required position) exposed)
                (let opened := revealCache table (required position) exposed
                 let payload := GroupedBalancedGraphPayload67.payload
                   (GroupedBalancedGraphMonitorTable67.privateOf
                     (knownTable opened))
                   (GroupedBalancedGraphMonitorTable67.labelsOf
                     (knownTable opened)) position
                 if query = position.input payload then
                   .reveal (.inl position) (fun answer =>
                     .done (answer,
                       opened.cacheQuery (.inl position) answer, residual))
                 else residualStep opened residual query (.inl position)
                   (fun answer opened updated =>
                     .done (answer, opened, updated))) := by
          simp only [publicStep, located, chain, if_false]
          exact GroupedBalancedGraphMonitorSetup67.run_disclose table
            (required position) exposed _
        rw [disclosed] at member
        let opened := revealCache table (required position) exposed
        let payload := GroupedBalancedGraphPayload67.payload
          (GroupedBalancedGraphMonitorTable67.privateOf
            (knownTable opened))
          (GroupedBalancedGraphMonitorTable67.labelsOf
            (knownTable opened)) position
        by_cases exact : query = position.input payload
        · simp only [opened, payload, exact, if_true, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact Or.inl rfl
        · have converted : result ∈ support (run table opened
              (residualStep opened residual query (.inl position)
                (fun answer exposed updated =>
                  .done (answer, exposed, updated)))) := by
            simpa only [opened, payload, exact, if_false] using member
          exact residualStep_frame table opened residual query
            (.inl position) result converted

#print axioms residualStep_frame
#print axioms chainStep_frame
#print axioms publicStep_frame

end SigGolfCandidate.Hypertree.GroupedBalancedGraphPublicResidualFrame67
