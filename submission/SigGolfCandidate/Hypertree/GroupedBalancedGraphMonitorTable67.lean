import SigGolfCandidate.Hypertree.GroupedBalancedGraphSampling67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrder67
import SigGolfCandidate.Hypertree.GroupedGraphMonitorFactors
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorFactors67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphUniform67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphUniform67
open SigGolf OracleComp OracleSpec Reference GroupedBalancedSecurityGraph67
  GroupedBalancedGraphSampling67 GroupedBalancedGraphOrder67



/-- Resampling every listed coordinate makes its initial value irrelevant. -/
theorem sampleLabels_congr_initial (positions : List Position) (first second : Labels)
    (outside : ∀ position ∉ positions, first position = second position) :
    sampleLabels positions first = sampleLabels positions second := by
  induction positions generalizing first second with
  | nil =>
    have same : first = second := funext fun position => outside position (by simp)
    rw [same]
  | cons position rest ih =>
    simp only [sampleLabels]
    congr 1
    funext answer
    apply ih
    intro other absent
    by_cases same : other = position
    · subst other
      simp
    · simp only [Function.update_of_ne same]
      exact outside other (by simp [same, absent])

/-- Resampling any finite list of coordinates preserves the uniform table law. -/
theorem uniform_resampling (positions : List Position) :
    𝒮[do let labels ← $ᵗ Labels; sampleLabels positions labels] = 𝒮[$ᵗ Labels] := by
  induction positions with
  | nil => simp [sampleLabels]
  | cons position rest ih =>
    calc
      _ = 𝒮[do
        let answer ← $ᵗ BitVec 256
        let labels ← $ᵗ Labels
        sampleLabels rest (Function.update labels position answer)] := by
          exact evalSPMF_bind_bind_swap _ _ _
      _ = 𝒮[do
        let updated ← (do
          let answer ← $ᵗ BitVec 256
          let labels ← $ᵗ Labels
          pure (Function.update labels position answer))
        sampleLabels rest updated] := by simp only [bind_assoc, pure_bind]
      _ = 𝒮[do let labels ← $ᵗ Labels; sampleLabels rest labels] := by
          rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]
      _ = _ := ih

/-- The complete graph has independent uniform full-width labels. -/
theorem sampleLabels_complete (initial : Labels) :
    𝒮[sampleLabels positions initial] = 𝒮[$ᵗ Labels] := by
  have independent (other : Labels) : sampleLabels positions other = sampleLabels positions initial :=
    sampleLabels_congr_initial positions other initial (fun position absent =>
      False.elim (absent (positions_complete position)))
  have equal : 𝒮[do let labels ← $ᵗ Labels; sampleLabels positions labels] =
      𝒮[sampleLabels positions initial] := by
    simp_rw [independent]
    apply evalSPMF_ext
    intro output
    rw [probOutput_bind_const]
    simp
  rw [← equal]
  exact uniform_resampling positions

/-- Exact joint law of all canonical labels and the oracle cache, with the actual
reference input at each vertex. This is a distribution identity, not a claim that
the candidate performs uncharged extra hash calls. -/
theorem run_complete_graph (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers) (initial : Labels) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (GroupedSecurityGraph.readGraph (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)).run ∅] =
      𝒮[do
        let labels ← $ᵗ Labels
        return (labels, graphCache privateAnswers positions labels ∅)] := by
  rw [run_readGraph_eq_labels_cache privateAnswers positions positions_nodup positions_ordered initial]
  simp only [evalSPMF_bind]
  rw [sampleLabels_complete]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphUniform67

end

/-! A uniform full-width point table supplies every public graph label and
private source used by the direct 67-chain monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGlobalPaired67

def labelsOf (table : PointTable) : GroupedBalancedSecurityGraph67.Labels :=
  fun position => table (.inl position)

def upperSources (table : PointTable) : SourceTable :=
  fun address chain => truncate (table (.inr (.inr (address, chain))))

def privateOf (table : PointTable) : GroupedBalancedGraphPayload67.PrivateAnswers where
  bottom := fun index => table (.inr (.inl index))
  upper := fun base leaf pair =>
    globalUnsplit (upperSources table, fun _ => 0) (base, leaf) pair

theorem bottom_source (table : PointTable) (index : BitVec 160) :
    (privateOf table).bottom index = table (.inr (.inl index)) := rfl

theorem upper_source (table : PointTable) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedGraphPayload67.chainSource (privateOf table) base leaf chain =
      truncate (table (.inr (.inr ((base, leaf), chain)))) := by
  change globalSources (globalUnsplit (upperSources table, fun _ => 0))
    (base, leaf) chain = upperSources table (base, leaf) chain
  rw [globalSources_unsplit]

@[simp] theorem labelsOf_fromPairs (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : GroupedBalancedGraphMonitorFactors67.BottomTable)
    (pairs : PairTable) (ghosts : GhostTable) :
    labelsOf (GroupedBalancedGraphMonitorFactors67.fromPairs labels bottom pairs ghosts) =
      labels := by
  funext position
  rfl

@[simp] theorem bottom_fromPairs (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : GroupedBalancedGraphMonitorFactors67.BottomTable)
    (pairs : PairTable) (ghosts : GhostTable) (index : BitVec 160) :
    (privateOf (GroupedBalancedGraphMonitorFactors67.fromPairs labels bottom pairs ghosts)).bottom
      index = bottom index := rfl

theorem upper_source_fromPairs (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : GroupedBalancedGraphMonitorFactors67.BottomTable)
    (pairs : PairTable) (ghosts : GhostTable)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedGraphPayload67.chainSource
      (privateOf (GroupedBalancedGraphMonitorFactors67.fromPairs labels bottom pairs ghosts))
      base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        ⟨bottom, fun b l p => pairs (b, l) p⟩ base leaf chain := by
  rw [upper_source]
  exact GroupedBalancedGraphMonitorFactors67.upper_secret_value
    labels bottom pairs ghosts base leaf chain

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67
