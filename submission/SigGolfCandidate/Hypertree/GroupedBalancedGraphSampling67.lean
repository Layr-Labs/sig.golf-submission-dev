import SigGolfCandidate.Hypertree.GroupedBalancedGraphConsistency67

/-! Rank-ordered grouped graph sampling can draw all public labels first and
then populate the query cache from those labels. The cache and labels remain
coupled in the joint distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphSampling67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphOrder67
open GroupedBalancedGraphCausality67

noncomputable def sampleLabels :
    List Position → GroupedBalancedSecurityGraph67.Labels →
      ProbComp GroupedBalancedSecurityGraph67.Labels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← $ᵗ BitVec 256
      sampleLabels rest (Function.update labels position answer)

def graphCache (privateAnswers : PrivateAnswers) :
    List Position → GroupedBalancedSecurityGraph67.Labels →
      QueryCache HashSpec → QueryCache HashSpec
  | [], _, cache => cache
  | position :: rest, labels, cache =>
      graphCache privateAnswers rest labels
        (cache.cacheQuery (graphInput privateAnswers labels position)
          (labels position))

theorem sampleLabels_unchanged (positions : List Position)
    (labels output : GroupedBalancedSecurityGraph67.Labels)
    (member : output ∈ support (sampleLabels positions labels))
    (position : Position) (absent : position ∉ positions) :
    output position = labels position := by
  induction positions generalizing labels with
  | nil =>
      have equal : output = labels := by simpa [sampleLabels] using member
      exact congrArg (fun values : GroupedBalancedSecurityGraph67.Labels => values position) equal
  | cons next rest ih =>
      rw [sampleLabels, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      have notNext : position ≠ next := fun same => absent (by simp [same])
      have notRest : position ∉ rest :=
        fun occurrence => absent (List.mem_cons_of_mem _ occurrence)
      rw [ih _ member notRest]
      exact Function.update_of_ne notNext _ _

theorem sampleLabels_input_preserved (privateAnswers : PrivateAnswers)
    (position : Position) (positions : List Position)
    (later : ∀ next ∈ positions, rank position ≤ rank next)
    (labels output : GroupedBalancedSecurityGraph67.Labels)
    (member : output ∈ support (sampleLabels positions labels)) :
    graphInput privateAnswers output position =
      graphInput privateAnswers labels position := by
  unfold graphInput
  apply congrArg position.input
  apply payload_congr
  intro child earlier
  apply sampleLabels_unchanged positions labels output member child
  intro occurs
  have bound := later child occurs
  omega

theorem sampleGraph_eq_labels_cache (privateAnswers : PrivateAnswers)
    (positions : List Position) (distinct : positions.Nodup)
    (ordered : positions.Pairwise
      (fun first second => rank first ≤ rank second))
    (labels : GroupedBalancedSecurityGraph67.Labels) (cache : QueryCache HashSpec) :
    𝒮[GroupedSecurityGraph.sampleGraph (payload privateAnswers) positions labels cache] =
      𝒮[do
        let final ← sampleLabels positions labels
        return (final, graphCache privateAnswers positions final cache)] := by
  induction positions generalizing labels cache with
  | nil => simp [GroupedSecurityGraph.sampleGraph, sampleLabels, graphCache]
  | cons first rest ih =>
      obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
      calc
        _ = 𝒮[do
          let answer ← $ᵗ BitVec 256
          let final ← sampleLabels rest (Function.update labels first answer)
          return (final, graphCache privateAnswers rest final
            (cache.cacheQuery (graphInput privateAnswers labels first) answer))] := by
              simp only [GroupedSecurityGraph.sampleGraph]
              apply evalSPMF_bind_congr
              intro answer _
              exact ih restDistinct restOrdered _ _
        _ = _ := by
          simp only [sampleLabels, bind_assoc]
          apply evalSPMF_bind_congr
          intro answer _
          apply evalSPMF_bind_congr
          intro final member
          have sameInput : graphInput privateAnswers final first =
              graphInput privateAnswers labels first := by
            exact (sampleLabels_input_preserved privateAnswers first rest
              firstBefore _ final member).trans
              (graphInput_update_of_rank privateAnswers first first le_rfl labels answer)
          have sameLabel : final first = answer := by
            exact (sampleLabels_unchanged rest _ final member first notRest).trans
              (Function.update_self first answer labels)
          simp only [graphCache]
          rw [sameInput, sameLabel]

theorem run_readGraph_eq_labels_cache (privateAnswers : PrivateAnswers)
    (positions : List Position) (distinct : positions.Nodup)
    (ordered : positions.Pairwise
      (fun first second => rank first ≤ rank second))
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels)).run ∅] =
      𝒮[do
        let final ← sampleLabels positions labels
        return (final, graphCache privateAnswers positions final ∅)] := by
  rw [GroupedSecurityGraph.run_readGraph_eq_sampleGraph (payload privateAnswers) positions
    distinct labels ∅ (by intros; rfl)]
  exact sampleGraph_eq_labels_cache privateAnswers positions
    distinct ordered labels ∅

end SigGolfCandidate.Hypertree.GroupedBalancedGraphSampling67
