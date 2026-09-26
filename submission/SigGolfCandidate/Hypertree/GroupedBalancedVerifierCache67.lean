import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCompose67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67

/-! Hash-only verifier execution under the stopped graph monitor retains all
previous lazy-oracle answers and its own first H5 index answer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierCache67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorInvariant67
open GroupedBalancedGraphMonitorCompose67
open GroupedBalancedGraphMonitorPublicCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

abbrev Result (α : Type) :=
  α × QueryCache PointSpec × QueryCache HashSpec

noncomputable def compile {α : Type} (program : OracleComp HashSpec α) :
    QueryCache PointSpec → QueryCache HashSpec → Program (Result α) :=
  OracleComp.construct
    (fun value exposed residual => .done (value, exposed, residual))
    (fun query _ next exposed residual =>
      GroupedBalancedGraphMonitorOracle67.publicStep exposed residual query
        (fun answer opened cache => next answer opened cache)) program

@[simp] theorem compile_pure {α : Type} (value : α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) :
    compile (pure value) exposed cache = .done (value, exposed, cache) := rfl

theorem compile_query {α : Type} (query : Query)
    (next : BitVec 256 → OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) :
    compile (liftM (HashSpec.query query) >>= next) exposed cache =
      GroupedBalancedGraphMonitorOracle67.publicStep exposed cache query
        (fun answer opened residual => compile (next answer) opened residual) := rfl

theorem random_preserves (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((randomOracle (spec := HashSpec) query).run cache))
    (old : Query) (value : BitVec 256)
    (present : cache old = some value) :
    result.2 old = some value := by
  cases found : cache query with
  | some answer =>
      simp only [randomOracle.run_eq, found, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      exact present
  | none =>
      simp only [randomOracle.run_eq, found, bind_pure_comp,
        support_map, Set.mem_image] at member
      obtain ⟨answer, _, same⟩ := member
      cases same
      have different : old ≠ query := by
        intro equal
        subst old
        rw [found] at present
        cases present
      simpa only [QueryCache.cacheQuery_of_ne _ _ different] using present

theorem random_present (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((randomOracle (spec := HashSpec) query).run cache)) :
    result.2 query = some result.1 := by
  cases found : cache query with
  | some answer =>
      simp only [randomOracle.run_eq, found, support_pure,
        Set.mem_singleton_iff] at member
      subst result
      exact found
  | none =>
      simp only [randomOracle.run_eq, found, bind_pure_comp,
        support_map, Set.mem_image] at member
      obtain ⟨answer, _, same⟩ := member
      cases same
      exact QueryCache.cacheQuery_self ..

theorem query_preserves (table : PointTable)
    (query : Query) (cache : QueryCache HashSpec)
    (result : BitVec 256 × QueryCache HashSpec)
    (member : result ∈ support
      ((GroupedBalancedGraphOracle67.publicOracle
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) query).run cache))
    (old : Query) (value : BitVec 256)
    (present : cache old = some value) :
    result.2 old = some value := by
  cases canonical : GroupedBalancedGraphOracle67.canonical
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) query with
  | some answer =>
      simp only [GroupedBalancedGraphOracle67.publicOracle, canonical,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact present
  | none =>
      simp only [GroupedBalancedGraphOracle67.publicOracle, canonical] at member
      exact random_preserves query cache result member old value present

theorem completed_preserves {α : Type} (table : PointTable)
    (signed : Finset (BitVec 160))
    (program : OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result α)
    (member : some result ∈ support
      (stopped table exposed (compile program exposed cache)))
    (old : Query) (value : BitVec 256)
    (present : cache old = some value) :
    result.2.2 old = some value := by
  induction program using OracleComp.inductionOn
      generalizing exposed cache with
  | pure answer =>
      simp only [compile_pure, stopped, support_pure,
        Set.mem_singleton_iff, Option.some.injEq] at member
      subst result
      exact present
  | query_bind query next ih =>
      rw [compile_query, stopped_public_bind table signed exposed cache initial,
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
          exact ih answer.1 answer.2.1 answer.2.2 nextSafe tail
            (query_preserves table query cache
              (answer.1, answer.2.2) spec.2.2.2 old value present)

theorem first_present {α : Type} (table : PointTable)
    (signed : Finset (BitVec 160))
    (query : Query) (next : BitVec 256 → OracleComp HashSpec α)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result α)
    (member : some result ∈ support
      (stopped table exposed
        (compile (liftM (HashSpec.query query) >>= next) exposed cache)))
    (noncanonical : GroupedBalancedGraphOracle67.canonical
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) query = none) :
    result.2.2 query ≠ none := by
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
      have sampled := spec.2.2.2
      simp only [GroupedBalancedGraphOracle67.publicOracle,
        noncanonical] at sampled
      have nextSafe :=
        GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
          table signed exposed cache initial query answer queried
      have present := completed_preserves table signed
        (next answer.1) answer.2.1 answer.2.2 nextSafe
        result tail query answer.1
        (random_present query cache _ sampled)
      rw [present]
      exact Option.some_ne_none _

theorem verifier_index_present (table : PointTable)
    (signed : Finset (BitVec 160))
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (initial : Safe table signed exposed cache)
    (result : Result Bool)
    (member : some result ∈ support
      (stopped table exposed
        (compile (GroupedBalancedVerifyOracle67.verify
          pk message signature) exposed cache))) :
    result.2.2
      (SecurityRandomOracle.indexInput message signature.randomizer) ≠ none := by
  apply first_present table signed
    (SecurityRandomOracle.indexInput message signature.randomizer)
    _ exposed cache initial result
  · simpa only [GroupedBalancedVerifyOracle67.verify,
      SecurityReference.ask, SecurityRandomOracle.indexInput] using member
  · simp only [GroupedBalancedGraphOracle67.canonical,
      GroupedBalancedGraphHonestSignView67.locate_index_none]

#print axioms verifier_index_present

end SigGolfCandidate.Hypertree.GroupedBalancedVerifierCache67
