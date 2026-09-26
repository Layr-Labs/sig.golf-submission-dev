import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPublicCoupling67

/-! The stopped public-query handler composes with arbitrary continuations and
retains the exact cache state needed for adaptive adversaries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompose67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67 GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorPublicCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

abbrev Answer := BitVec 256 × QueryCache PointSpec × QueryCache HashSpec

noncomputable def continueWith {α : Type} (table : PointTable)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    Option Answer → ProbComp (Option α)
  | none => pure none
  | some result => stopped table result.2.1
      (next result.1 result.2.1 result.2.2)

theorem stopped_public_bind {α : Type} (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    stopped table exposed
      (GroupedBalancedGraphMonitorOracle67.publicStep exposed cache query next) =
      (stopped table exposed
        (GroupedBalancedGraphMonitorOracle67.publicStep exposed cache query
          (fun answer opened residual => .done (answer, opened, residual))) >>=
        continueWith table next) := by
  rw [stopped_public_oracle table exposed cache query next initial.1 initial.2.2,
    stopped_public_oracle table exposed cache query
      (fun answer opened residual => .done (answer, opened, residual))
      initial.1 initial.2.2]
  by_cases first : inputHit table exposed query
  · simp only [if_pos first, pure_bind, continueWith]
  · simp only [if_neg first, bind_assoc]
    apply bind_congr
    intro result
    by_cases second : outputHit table query result.1
    · simp only [if_pos second, pure_bind, continueWith]
    · simp only [if_neg second, stopped, pure_bind, continueWith]

theorem read_spec (table : PointTable)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signedBottom exposed cache)
    (query : Query) (result : Answer)
    (member : some result ∈ support (stopped table exposed
      (GroupedBalancedGraphMonitorOracle67.publicStep exposed cache query
        (fun answer opened residual => .done (answer, opened, residual))))) :
    ¬inputHit table exposed query ∧
      ¬outputHit table query result.1 ∧
      result.2.1 = opened table exposed query ∧
      (result.1, result.2.2) ∈ support
        ((GroupedBalancedGraphOracle67.publicOracle
          (GroupedBalancedGraphMonitorTable67.privateOf table)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache) := by
  rw [stopped_public_oracle table exposed cache query _
    initial.1 initial.2.2] at member
  by_cases first : inputHit table exposed query
  · simp only [if_pos first, support_pure,
      Set.mem_singleton_iff, Option.some_ne_none] at member
  · rw [if_neg first, mem_support_bind_iff] at member
    obtain ⟨answer, queried, after⟩ := member
    by_cases second : outputHit table query answer.1
    · simp only [if_pos second, support_pure,
        Set.mem_singleton_iff, Option.some_ne_none] at after
    · simp only [if_neg second, stopped, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at after
      subst result
      exact ⟨first, second, rfl, queried⟩

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompose67
