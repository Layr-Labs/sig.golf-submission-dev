import SigGolfCandidate.Hypertree.GroupedBalancedGraphQuery67
import SigGolfCandidate.Hypertree.SecurityCache

/-! Embedding the complete grouped public graph in a lazy random-oracle cache
is equivalent, for every adaptive program, to a public graph oracle backed by
an independent residual cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphOracle67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphOrder67
open GroupedBalancedGraphSampling67 GroupedBalancedGraphQuery67 GroupedBalancedGraphCausality67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def canonical (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) (query : Query) :
    Option (BitVec 256) :=
  match locate query with
  | none => none
  | some position => if query = graphInput privateAnswers labels position
      then some (labels position) else none

noncomputable def embed (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (residual : QueryCache HashSpec) : QueryCache HashSpec :=
  graphCache privateAnswers positions labels residual

theorem canonical_eq_cache (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) (query : Query) :
    canonical privateAnswers labels query =
      graphCache privateAnswers positions labels ∅ query :=
  (complete_cache_lookup privateAnswers labels query).symm

theorem programmed_hash (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) (residual : Hash)
    (query : Query) :
    GroupedBalancedGraphProgramming67.programmed
      (payload privateAnswers labels) labels residual query =
      match canonical privateAnswers labels query with
      | some answer => answer
      | none => residual query := by
  rw [GroupedBalancedGraphQuery67.locate_programmed]
  unfold canonical
  cases located : locate query with
  | none => rfl
  | some position =>
      change (if query = position.input (payload privateAnswers labels position)
        then labels position else residual query) =
        (match (if query = position.input (payload privateAnswers labels position)
          then some (labels position) else none) with
          | some answer => answer
          | none => residual query)
      by_cases same : query = position.input (payload privateAnswers labels position)
      · simp only [if_pos same]
      · simp only [if_neg same]

theorem embed_lookup (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (residual : QueryCache HashSpec) (query : Query) :
    embed privateAnswers labels residual query =
      match canonical privateAnswers labels query with
      | some answer => some answer
      | none => residual query := by
  rw [canonical_eq_cache]
  by_cases found : ∃ position : Position,
      query = graphInput privateAnswers labels position
  · obtain ⟨position, same⟩ := found
    rw [same, embed,
      graphCache_inside privateAnswers positions labels residual position
        (positions_complete position),
      graphCache_inside privateAnswers positions labels ∅ position
        (positions_complete position)]
  · have outside : ∀ position ∈ positions,
        query ≠ graphInput privateAnswers labels position :=
      fun position _ same => found ⟨position, same⟩
    rw [embed,
      graphCache_outside privateAnswers positions labels residual query outside,
      graphCache_outside privateAnswers positions labels ∅ query outside]
    rfl

theorem embed_cacheQuery (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (residual : QueryCache HashSpec) (query : Query) (answer : BitVec 256)
    (outside : canonical privateAnswers labels query = none) :
    embed privateAnswers labels (residual.cacheQuery query answer) =
      (embed privateAnswers labels residual).cacheQuery query answer := by
  ext other
  by_cases same : other = query
  · subst other
    rw [embed_lookup, outside, QueryCache.cacheQuery_self,
      QueryCache.cacheQuery_self]
  · rw [embed_lookup, QueryCache.cacheQuery_of_ne _ _ same,
      QueryCache.cacheQuery_of_ne _ _ same, embed_lookup]

noncomputable def publicOracle (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  fun query => match canonical privateAnswers labels query with
  | some answer => pure answer
  | none => randomOracle query

theorem query_run (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (residual : QueryCache HashSpec) (query : Query) :
    (randomOracle (spec := HashSpec) query).run
      (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (publicOracle privateAnswers labels query).run residual := by
  cases graph : canonical privateAnswers labels query with
  | some answer =>
      simp only [randomOracle.run_eq, embed_lookup, graph,
        publicOracle, StateT.run_pure, map_pure]
  | none =>
      simp only [randomOracle.run_eq, embed_lookup, graph, publicOracle]
      cases cached : residual query with
      | some answer => simp only [map_pure]
      | none =>
          simp only [map_bind, map_pure]
          apply bind_congr
          intro answer
          rw [embed_cacheQuery privateAnswers labels residual query answer graph]

noncomputable def implementation (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + publicOracle privateAnswers labels

theorem world_query_run (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (residual : QueryCache HashSpec) (query : World.Domain) :
    (SecurityCache.implementation query).run
      (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (implementation privateAnswers labels query).run residual := by
  cases query with
  | inl coin =>
      change ((fun answer => (answer, embed privateAnswers labels residual)) <$>
        (liftM (unifSpec.query coin) : ProbComp _)) =
        (fun result => (result.1, embed privateAnswers labels result.2)) <$>
          ((fun answer => (answer, residual)) <$>
            (liftM (unifSpec.query coin) : ProbComp _))
      rw [Functor.map_map]
  | inr input => exact query_run privateAnswers labels residual input

theorem simulate_run (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    {α : Type} (program : OracleComp World α)
    (residual : QueryCache HashSpec) :
    (simulateQ SecurityCache.implementation program).run
      (embed privateAnswers labels residual) =
      (fun result => (result.1, embed privateAnswers labels result.2)) <$>
        (simulateQ (implementation privateAnswers labels) program).run residual := by
  induction program using OracleComp.inductionOn generalizing residual with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind,
        world_query_run, bind_map_left, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2

theorem observe_eq (privateAnswers : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    {α : Type} (program : OracleComp World α)
    (residual : QueryCache HashSpec) :
    (simulateQ SecurityCache.implementation program).run'
      (embed privateAnswers labels residual) =
    (simulateQ (implementation privateAnswers labels) program).run' residual := by
  rw [StateT.run'_eq, simulate_run, Functor.map_map]
  rfl

end SigGolfCandidate.Hypertree.GroupedBalancedGraphOracle67
