import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorProgram67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorStop67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorResidual67. -/
section
/-! Stop at the first contact for coupling while retaining the exact passive
experiment as the event whose probability is bounded. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorStop67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
set_option backward.isDefEq.respectTransparency false

noncomputable def stopped {α : Type} (table : PointTable) :
    QueryCache PointSpec → Program α → ProbComp (Option α)
  | _, .done value => pure (some value)
  | cache, .reveal point next =>
      stopped table (cache.cacheQuery point (table point)) (next (table point))
  | cache, .guess point value next =>
      if cache point = none ∧ truncate (table point) = value then pure none
      else stopped table cache next
  | cache, .coin n next => do
      let value ← $ᵗ Fin (n + 1)
      stopped table cache (next value)
  | cache, .bits next => do
      let value ← $ᵗ BitVec 256
      stopped table cache (next value)
  | cache, .collision target next => do
      let value ← $ᵗ BitVec 256
      if truncate value = target then pure none
      else stopped table cache (next value)

def keep {α : Type} (result : Outcome α) : Option α :=
  if result.bad then none else some result.value

private theorem map_const_spmf {α β : Type} (program : ProbComp α) (value : β) :
    𝒮[(fun _ => value) <$> program] = 𝒮[(pure value : ProbComp β)] := by
  apply evalSPMF_ext
  intro output
  simp only [map_eq_pure_bind, probOutput_bind_const]
  simp

theorem stopped_eq {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α) :
    𝒮[stopped table cache program] = 𝒮[keep <$> run table cache program] := by
  induction program generalizing cache with
  | done value => simp [stopped, run, keep]
  | reveal point next ih => exact ih (table point) _
  | guess point value next ih =>
      unfold stopped run
      by_cases hit : cache point = none ∧ truncate (table point) = value
      · simp only [hit, if_true, decide_true, Functor.map_map]
        change 𝒮[pure none] = 𝒮[(fun _ => none) <$> run table cache next]
        exact (map_const_spmf _ _).symm
      · simp only [hit, if_false, decide_false, Functor.map_map]
        change 𝒮[stopped table cache next] = 𝒮[keep <$> run table cache next]
        exact ih cache
  | coin n next ih | bits next ih =>
      simp only [stopped, run, map_bind]
      apply evalSPMF_bind_congr
      intro value _
      exact ih value cache
  | collision target next ih =>
      simp only [stopped, run, map_bind]
      apply evalSPMF_bind_congr
      intro value _
      by_cases hit : truncate value = target
      · simp only [hit, if_true, decide_true, Functor.map_map]
        change 𝒮[pure none] = 𝒮[(fun _ => none) <$> run table cache (next value)]
        exact (map_const_spmf _ _).symm
      · simp only [hit, if_false, decide_false, Functor.map_map]
        change 𝒮[stopped table cache (next value)] =
          𝒮[keep <$> run table cache (next value)]
        exact ih value cache

theorem stopped_none {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α) :
    Pr[= none | stopped table cache program] =
      Pr[fun result => result.bad = true | run table cache program] := by
  rw [probOutput_def, stopped_eq, ← probOutput_def, probOutput_map]
  congr 1
  funext result
  simp [keep]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorStop67

end

/-! Residual-query coupling for the grouped output-retaining monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorResidual67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
set_option backward.isDefEq.respectTransparency false

def Agree (table : PointTable) (exposed : QueryCache PointSpec) : Prop :=
  ∀ point answer, exposed point = some answer → answer = table point

def CacheMissTarget (cache : QueryCache HashSpec)
    (query : Query) (target : Digest) : Prop :=
  ∀ answer, cache query = some answer → truncate answer ≠ target

theorem Agree.cacheQuery (table : PointTable)
    (exposed : QueryCache PointSpec) (agree : Agree table exposed)
    (point : Point) :
    Agree table (exposed.cacheQuery point (table point)) := by
  intro other answer known
  by_cases same : other = point
  · subst other
    simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using known.symm
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at known
    exact agree other answer known

theorem agree_revealCache (table : PointTable) (points : List Point)
    (exposed : QueryCache PointSpec) (agree : Agree table exposed) :
    Agree table (revealCache table points exposed) := by
  induction points generalizing exposed with
  | nil => exact agree
  | cons point rest ih =>
      apply ih _
      intro other answer known
      by_cases same : other = point
      · subst other
        simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using known.symm
      · rw [QueryCache.cacheQuery_of_ne _ _ same] at known
        exact agree other answer known

theorem stopped_disclose {α : Type} (table : PointTable)
    (points : List Point) (exposed : QueryCache PointSpec)
    (next : QueryCache PointSpec → GroupedBalancedGraphMonitorProgram67.Program α) :
    stopped table exposed (disclose points exposed next) =
      stopped table (revealCache table points exposed)
        (next (revealCache table points exposed)) := by
  induction points generalizing exposed with
  | nil => rfl
  | cons point rest ih => exact ih (exposed.cacheQuery point (table point))

theorem stopped_residualStep {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α)
    (agree : Agree table exposed)
    (clean : CacheMissTarget residual query (truncate (table target))) :
    stopped table exposed
      (residualStep exposed residual query target next) =
    (do
      let result ← (randomOracle (spec := HashSpec) query).run residual
      if truncate result.1 = truncate (table target) then pure none
      else stopped table exposed (next result.1 exposed result.2)) := by
  cases cached : residual query with
  | some answer =>
      have miss := clean answer cached
      simp only [residualStep, cached, stopped, randomOracle.run_eq,
        pure_bind, if_neg miss]
  | none =>
      cases known : exposed target with
      | some answer =>
          have same := agree target answer known
          simp only [residualStep, cached, known, stopped, randomOracle.run_eq,
            bind_assoc, pure_bind, same]
      | none =>
          simp only [residualStep, cached, known, stopped, randomOracle.run_eq,
            bind_assoc, pure_bind]
          apply bind_congr
          intro answer
          simp only [known, true_and, eq_comm]

theorem stopped_outside {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α)
    (located : GroupedBalancedGraphQuery67.locate query = none) :
    stopped table exposed
      (publicStep exposed residual query next) =
    (do
      let result ← (randomOracle (spec := HashSpec) query).run residual
      stopped table exposed (next result.1 exposed result.2)) := by
  cases cached : residual query with
  | some answer =>
      simp only [publicStep, located, cached, stopped, randomOracle.run_eq,
        pure_bind]
  | none =>
      simp only [publicStep, located, cached, stopped, randomOracle.run_eq,
        bind_assoc, pure_bind]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorResidual67
