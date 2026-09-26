import SigGolfCandidate.Hypertree.GroupedBalancedSecurityPrivatePresample67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateGraphDisjoint67

/-! The private H1/nonce sources and the entire direct67 public graph can be
sampled together in the shared random-oracle cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPresample67
open SigGolf OracleComp OracleSpec Reference SecurityCache
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphSampling67
open GroupedBalancedGraphOrder67 GroupedBalancedSecurityPrivatePresample67
open GroupedBalancedPrivateDerivation67 GroupedBalancedPrivateFactors67
open scoped Classical

def privateOfAnswers (answers : PrivateTable) :
    GroupedBalancedGraphPayload67.PrivateAnswers where
  bottom := fun index => answers (.bottom index)
  upper := fun base leaf pair => answers (.upper base leaf pair)

def IsSource : Slot → Prop
  | .bottom _ => True
  | .upper _ _ _ => True
  | .randomizer _ => False

noncomputable def sourceSlots : List Slot :=
  (Finset.univ.filter IsSource).toList

theorem sourceSlots_nodup : sourceSlots.Nodup := Finset.nodup_toList _

theorem mem_sourceSlots (slot : Slot) : slot ∈ sourceSlots ↔ IsSource slot := by
  simp [sourceSlots]

noncomputable def sourceCache (secretKey : SecretKey)
    (answers : PrivateTable) : QueryCache HashSpec :=
  populate secretKey sourceSlots answers ∅

theorem source_presampling {α : Type} (secretKey : SecretKey)
    (program : OracleComp World α) :
    𝒮[SecurityGraphHidden.observe program ∅] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        SecurityGraphHidden.observe program (sourceCache secretKey answers)] := by
  exact (populate_presampling secretKey sourceSlots sourceSlots_nodup
    program ∅ (by intros; rfl)).symm

theorem source_cache_other (secretKey : SecretKey)
    (answers : PrivateTable) (query : Query)
    (outside : ∀ slot : Slot, IsSource slot →
      query ≠ input secretKey slot) :
    sourceCache secretKey answers query = none := by
  rw [sourceCache, populate_other secretKey sourceSlots answers ∅ query
    (fun slot member => outside slot ((mem_sourceSlots slot).mp member))]
  rfl

theorem source_cache_lookup (secretKey : SecretKey)
    (answers : PrivateTable) (slot : Slot) (source : IsSource slot) :
    sourceCache secretKey answers (input secretKey slot) =
      some (answers slot) := by
  exact populate_lookup secretKey sourceSlots sourceSlots_nodup answers ∅
    slot ((mem_sourceSlots slot).mpr source)

theorem source_cache_randomizer_none (secretKey : SecretKey)
    (answers : PrivateTable) (message : Message) :
    sourceCache secretKey answers
      (input secretKey (.randomizer message)) = none := by
  apply source_cache_other
  intro slot source same
  have sameSlot : Slot.randomizer message = slot :=
    input_injective secretKey same
  cases slot with
  | bottom _ => cases sameSlot
  | upper _ _ _ => cases sameSlot
  | randomizer _ => cases source

theorem graph_fresh_after_private (secretKey : SecretKey)
    (answers : PrivateTable) (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (position : Position) (labels : Labels) :
    populate secretKey allSlots answers ∅
      (position.input (GroupedBalancedGraphPayload67.payload privateAnswers labels position)) =
      none := by
  apply all_private_other
  intro slot
  exact (GroupedBalancedPrivateGraphDisjoint67.input_ne_public_graph
    secretKey slot position _).symm

theorem graph_fresh_after_source (secretKey : SecretKey)
    (answers : PrivateTable) (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (position : Position) (labels : Labels) :
    sourceCache secretKey answers
      (position.input (GroupedBalancedGraphPayload67.payload privateAnswers labels position)) =
      none := by
  apply source_cache_other
  intro slot _
  exact (GroupedBalancedPrivateGraphDisjoint67.input_ne_public_graph
    secretKey slot position _).symm

/-- The complete public graph remains independent and uniform even after all
direct67 private derivation cells are populated in the same oracle cache. -/
theorem run_graph_after_private (secretKey : SecretKey)
    (answers : PrivateTable)
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (initial : Labels) :
    let privateCache := populate secretKey allSlots answers ∅
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (GroupedSecurityGraph.readGraph
        (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)).run
        privateCache] =
      𝒮[do
        let labels ← $ᵗ Labels
        return (labels, graphCache privateAnswers positions labels privateCache)] := by
  dsimp only
  rw [GroupedSecurityGraph.run_readGraph_eq_sampleGraph
    (GroupedBalancedGraphPayload67.payload privateAnswers) positions
    positions_nodup initial (populate secretKey allSlots answers ∅)
    (by intro position _ labels
        exact graph_fresh_after_private secretKey answers privateAnswers position labels)]
  rw [sampleGraph_eq_labels_cache privateAnswers positions positions_nodup
    positions_ordered initial (populate secretKey allSlots answers ∅)]
  simp only [evalSPMF_bind]
  rw [GroupedBalancedGraphUniform67.sampleLabels_complete]

theorem run_graph_after_source (secretKey : SecretKey)
    (answers : PrivateTable)
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (initial : Labels) :
    let cache := sourceCache secretKey answers
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
      (GroupedSecurityGraph.readGraph
        (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)).run
        cache] =
      𝒮[do
        let labels ← $ᵗ Labels
        return (labels, graphCache privateAnswers positions labels cache)] := by
  dsimp only
  rw [GroupedSecurityGraph.run_readGraph_eq_sampleGraph
    (GroupedBalancedGraphPayload67.payload privateAnswers) positions
    positions_nodup initial (sourceCache secretKey answers)
    (by intro position _ labels
        exact graph_fresh_after_source secretKey answers privateAnswers position labels)]
  rw [sampleGraph_eq_labels_cache privateAnswers positions positions_nodup
    positions_ordered initial (sourceCache secretKey answers)]
  simp only [evalSPMF_bind]
  rw [GroupedBalancedGraphUniform67.sampleLabels_complete]

/-- The graph sampling may be hidden behind an arbitrary observable
continuation even when the same oracle cache already holds every private H1
and nonce answer. Its output counters are unchanged. -/
theorem graph_after_private_presampling {α : Type}
    (secretKey : SecretKey) (answers : PrivateTable)
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (program : OracleComp World α) (initial : Labels) :
    let privateCache := populate secretKey allSlots answers ∅
    𝒮[SecurityGraphHidden.observe program privateCache] =
      𝒮[do
        let labels ← $ᵗ Labels
        SecurityGraphHidden.observe program
          (graphCache privateAnswers positions labels privateCache)] := by
  dsimp only
  rw [← SecurityGraphHidden.insert_prefix
    (GroupedSecurityGraph.readGraph
      (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)
    program (populate secretKey allSlots answers ∅)]
  rw [evalSPMF_bind, run_graph_after_private secretKey answers privateAnswers initial]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]

theorem graph_after_source_presampling {α : Type}
    (secretKey : SecretKey) (answers : PrivateTable)
    (privateAnswers : GroupedBalancedGraphPayload67.PrivateAnswers)
    (program : OracleComp World α) (initial : Labels) :
    let cache := sourceCache secretKey answers
    𝒮[SecurityGraphHidden.observe program cache] =
      𝒮[do
        let labels ← $ᵗ Labels
        SecurityGraphHidden.observe program
          (graphCache privateAnswers positions labels cache)] := by
  dsimp only
  rw [← SecurityGraphHidden.insert_prefix
    (GroupedSecurityGraph.readGraph
      (GroupedBalancedGraphPayload67.payload privateAnswers) positions initial)
    program (sourceCache secretKey answers)]
  rw [evalSPMF_bind, run_graph_after_source secretKey answers privateAnswers initial]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]

/-- Exact joint private-source/public-graph presampling for the actual shared
lazy random oracle. The continuation is arbitrary and its full result is kept. -/
theorem joint_presampling {α : Type} (secretKey : SecretKey)
    (program : OracleComp World α) (initial : Labels) :
    𝒮[SecurityGraphHidden.observe program ∅] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        let labels ← $ᵗ Labels
        SecurityGraphHidden.observe program
          (graphCache (privateOfAnswers answers) positions labels
            (populate secretKey allSlots answers ∅))] := by
  rw [all_private_presampling secretKey program]
  apply evalSPMF_bind_congr
  intro answers _
  exact graph_after_private_presampling secretKey answers
    (privateOfAnswers answers) program initial

/-- Source-only joint presampling leaves honest randomizer inputs lazy. This is
the form used when replacing the source cache in the organizer game. -/
theorem joint_source_presampling {α : Type} (secretKey : SecretKey)
    (program : OracleComp World α) (initial : Labels) :
    𝒮[SecurityGraphHidden.observe program ∅] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        let labels ← $ᵗ Labels
        SecurityGraphHidden.observe program
          (graphCache (privateOfAnswers answers) positions labels
            (sourceCache secretKey answers))] := by
  rw [source_presampling secretKey program]
  apply evalSPMF_bind_congr
  intro answers _
  exact graph_after_source_presampling secretKey answers
    (privateOfAnswers answers) program initial

#print axioms run_graph_after_private
#print axioms joint_presampling
#print axioms joint_source_presampling
#print axioms source_cache_randomizer_none

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPresample67
