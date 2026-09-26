import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorRequired67
import SigGolfCandidate.Hypertree.GroupedSecurityGraph
import SigGolfCandidate.Hypertree.SecurityGraphContact
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorMetadata67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedGraphContact; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCoupling67. -/
section
/-! A local grouped graph query can contact a hidden 128-bit predecessor by
guessing its canonical payload or by colliding with its truncated output.
The bound is two 128-bit tests, as in the binary monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedGraphContact
open SigGolf OracleComp OracleSpec Reference SecurityPacking SecurityExtraction
open GroupedSecurityGraph
open scoped Classical

def chainInput (position : Position) (point : Digest) : Query :=
  position.input (bytes point)

theorem chainInput_injective (position : Position) :
    Function.Injective (chainInput position) := by
  intro first second equal
  apply bytes_injective 16
  exact addressedInput_payload_injective _ _ _ _ _ _ equal

theorem prob_chain_input_guess (position : Position) (query : Query) :
    Pr[fun value : BitVec 256 => query = chainInput position (truncate value) |
      $ᵗ BitVec 256] ≤ 1 / 2 ^ 128 := by
  by_cases possible : ∃ point, query = chainInput position point
  · obtain ⟨point, equal⟩ := possible
    have event : (fun value : BitVec 256 =>
        query = chainInput position (truncate value)) =
        (fun value => value.extractLsb' 0 128 ∈ ({point} : Finset Digest)) := by
      funext value
      apply propext
      simp only [Finset.mem_singleton]
      constructor
      · intro matched
        exact (chainInput_injective position (equal.symm.trans matched)).symm
      · intro matched
        exact equal.trans (congrArg (chainInput position) matched.symm)
    rw [event, SecurityUniform.prob_extract_mem 128 128]
    simp
  · have event : (fun value : BitVec 256 =>
        query = chainInput position (truncate value)) =
        (fun _ => False) := by
      funext value
      apply propext
      exact ⟨fun equal => possible ⟨truncate value, equal⟩, False.elim⟩
    rw [event]
    simp

noncomputable def chainTrial (position : Position) (query : Query)
    (target : BitVec 256) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let hidden ← $ᵗ BitVec 256
  let canonical := chainInput position (truncate hidden)
  let result ← (randomOracle (spec := HashSpec) query).run
    (cache.cacheQuery canonical target)
  return decide (query = canonical ∨ truncate result.1 = truncate target)

theorem prob_chain_contact_le (position : Position) (query : Query)
    (target : BitVec 256) (cache : QueryCache HashSpec)
    (fresh : cache query = none) :
    Pr[fun hit => hit = true | chainTrial position query target cache] ≤
      2 / 2 ^ 128 := by
  unfold chainTrial
  have bound := probEvent_bind_le_probEvent_add
    (mx := ($ᵗ BitVec 256))
    (my := fun hidden => do
      let canonical := chainInput position (truncate hidden)
      let result ← (randomOracle (spec := HashSpec) query).run
        (cache.cacheQuery canonical target)
      return decide (query = canonical ∨ truncate result.1 = truncate target))
    (q := fun hit => hit = true)
    (p := fun hidden => query = chainInput position (truncate hidden))
    (ε := (1 : ENNReal) / 2 ^ 128) (by
      intro hidden _ different
      dsimp only
      rw [randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ different, fresh]
      simp only [bind_assoc, pure_bind]
      have exactProbability := SecurityUniform.prob_extract_mem 128 128
        ({truncate target} : Finset Digest)
      simp only [← map_eq_pure_bind, probEvent_map, Function.comp_def]
      change Pr[fun value : BitVec 256 =>
        decide (query = chainInput position (truncate hidden) ∨
          truncate value = truncate target) = true | $ᵗ BitVec 256] ≤ _
      simp only [different, false_or, decide_eq_true_eq]
      simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one,
        truncate] using exactProbability.le)
  calc
    _ ≤ Pr[fun value : BitVec 256 =>
          query = chainInput position (truncate value) | $ᵗ BitVec 256] +
          1 / 2 ^ 128 := bound
    _ ≤ 1 / 2 ^ 128 + 1 / 2 ^ 128 :=
      add_le_add (prob_chain_input_guess position query) le_rfl
    _ = _ := by simp only [div_eq_mul_inv]; ring

end SigGolfCandidate.Hypertree.GroupedGraphContact
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainState67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCoupling67. -/
section
/-! Local no-contact facts for the output-retaining grouped chain monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainState67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorPredecessor67

theorem parsed_payload_input (position : Position) (query : Query)
    (point : Digest)
    (parsed : parsedChainPayload position query = some point) :
    query = position.input (bytes point) := by
  unfold parsedChainPayload at parsed
  split at parsed
  next found =>
    cases Option.some.inj parsed
    exact found.choose_spec
  next absent => cases parsed

theorem parsed_payload_injective (position : Position) (query : Query)
    (first second : Digest)
    (firstParsed : parsedChainPayload position query = some first)
    (secondInput : query = position.input (bytes second)) :
    first = second := by
  exact GroupedGraphContact.chainInput_injective position
    ((parsed_payload_input position query first firstParsed).symm.trans secondInput)

theorem canonical_chain_input (table : PointTable) (position : Position)
    (tagTwo : position.val.tag.val = 2) (previous : Point)
    (located : predecessor position.val = some previous) :
    GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position =
    position.input (bytes (truncate (table previous))) := by
  unfold GroupedBalancedGraphCausality67.graphInput
  rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo,
    chain_payload_eq table position.val, located]

theorem hidden_miss_noncanonical (table : PointTable)
    (position : Position) (tagTwo : position.val.tag.val = 2)
    (previous : Point) (located : predecessor position.val = some previous)
    (query : Query) (point : Digest)
    (parsed : parsedChainPayload position query = some point)
    (missed : truncate (table previous) ≠ point) :
    query ≠ GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
  intro canonical
  rw [canonical_chain_input table position tagTwo previous located] at canonical
  exact missed (parsed_payload_injective position query point
    (truncate (table previous)) parsed canonical).symm

theorem known_matches_canonical (table : PointTable)
    (position : Position) (tagTwo : position.val.tag.val = 2)
    (previous : Point) (located : predecessor position.val = some previous)
    (query : Query) (point : Digest)
    (parsed : parsedChainPayload position query = some point) :
    query = GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position ↔
    point = truncate (table previous) := by
  rw [canonical_chain_input table position tagTwo previous located,
    parsed_payload_input position query point parsed]
  constructor
  · intro same
    exact GroupedGraphContact.chainInput_injective position same
  · intro same
    exact congrArg (fun value => position.input (bytes value)) same

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorChainState67

end

/-! Chain-query coupling, retaining the exact canonical predecessor in the
stopped semantics. A hidden predecessor can match only by a charged guess. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCoupling67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorOracle67 GroupedBalancedGraphMonitorStop67
open GroupedBalancedGraphMonitorResidual67 GroupedBalancedGraphMonitorPredecessor67
open GroupedBalancedGraphMonitorChainState67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

noncomputable def chainStopped {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α) : ProbComp (Option α) :=
  let target : Point := .inl position
  let canonical := match predecessor position.val with
    | none => position.input []
    | some previous => position.input (bytes (truncate (table previous)))
  if query = canonical then
    if match predecessor position.val with
      | none => False
      | some previous => exposed previous = none then pure none
    else
      let opened := exposed.cacheQuery target (table target)
      stopped table opened (next (table target) opened residual)
  else do
    let result ← (randomOracle (spec := HashSpec) query).run residual
    if truncate result.1 = truncate (table target) then pure none
    else stopped table exposed (next result.1 exposed result.2)

theorem parsed_none_not_input (position : Position) (query : Query)
    (point : Digest)
    (absent : parsedChainPayload position query = none) :
    query ≠ position.input (bytes point) := by
  intro same
  have found : ∃ candidate, query = position.input (bytes candidate) :=
    ⟨point, same⟩
  unfold parsedChainPayload at absent
  simp only [dif_pos found] at absent
  cases absent

theorem stopped_chain {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec →
      GroupedBalancedGraphMonitorProgram67.Program α)
    (tagTwo : position.val.tag.val = 2)
    (agree : Agree table exposed)
    (clean : CacheMissTarget residual query
      (truncate (table (.inl position)))) :
    stopped table exposed (chainStep exposed residual position query next) =
      chainStopped table exposed residual position query next := by
  have residualEq := stopped_residualStep table exposed residual query
    (.inl position) next agree clean
  unfold chainStep chainStopped
  cases located : predecessor position.val with
  | none =>
      by_cases matched : query = position.input []
      · simp only [located, if_pos matched, stopped, false_or,
          Bool.false_eq_true, ↓reduceIte]
      · simpa only [located, if_neg matched, Bool.false_eq_true,
          ↓reduceIte] using residualEq
  | some previous =>
      cases parsed : parsedChainPayload position query with
      | none =>
          have different := parsed_none_not_input position query
            (truncate (table previous)) parsed
          simpa only [located, parsed, if_neg different] using residualEq
      | some point =>
          have canonical := known_matches_canonical table position
            tagTwo previous located query point parsed
          rw [canonical_chain_input table position tagTwo previous located] at canonical
          cases known : exposed previous with
          | none =>
              by_cases hit : point = truncate (table previous)
              · have matched := canonical.mpr hit
                simp only [located, parsed, known, hit, if_pos matched,
                  stopped, true_and, if_true]
              · have different := fun same => hit (canonical.mp same)
                have missed : truncate (table previous) ≠ point := Ne.symm hit
                simpa only [located, parsed, known, if_neg different,
                  stopped, true_and, if_neg missed] using residualEq
          | some value =>
              have same := agree previous value known
              by_cases hit : point = truncate value
              · have matched := canonical.mpr (hit.trans (congrArg truncate same))
                simp only [located, parsed, known, hit, if_pos matched,
                  Option.some_ne_none, if_false, stopped]
                simp only [if_true, stopped]
              · have different : query ≠ position.input
                    (bytes (truncate (table previous))) := by
                  intro matched
                  exact hit ((canonical.mp matched).trans
                    (congrArg truncate same.symm))
                simpa only [located, parsed, known, if_neg hit,
                  if_neg different] using residualEq

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCoupling67
