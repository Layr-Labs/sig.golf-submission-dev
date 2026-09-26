import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrder67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphCausality67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphConsistency67. -/
section
/-! The grouped public graph is causal in rank order: a vertex payload reads
only labels at strictly lower rank. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphCausality67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphOrder67

theorem payload_congr (privateAnswers : PrivateAnswers) (position : Position)
    (first second : Labels)
    (same : ∀ child, rank child < rank position → first child = second child) :
    payload privateAnswers first position = payload privateAnswers second position := by
  by_cases tagTwo : position.val.tag.val = 2
  · simp only [payload, if_pos tagTwo]
    by_cases bottom : position.val.level.val = 0 ∧ position.val.leaf.val = 0 ∧
        position.val.chain.val = 0 ∧ position.val.step.val = 0
    · simp only [chainPayload, dif_pos bottom]
    · by_cases level : 10 ≤ position.val.level.val ∧ position.val.level.val < 160
      · by_cases leaf : position.val.leaf.val = 0
        · by_cases chainBound : position.val.chain.val < 67
          · by_cases stepBound : position.val.step.val < 10
            · by_cases zero : position.val.step.val = 0
              · simp only [chainPayload, dif_neg bottom, dif_pos level,
                  dif_pos leaf, dif_pos chainBound, dif_pos stepBound,
                  dif_pos zero]
              · let base : Fin 150 := ⟨position.val.level.val - 10, by omega⟩
                let leafIndex : BitVec 160 := BitVec.ofNat 160 position.val.tree.toNat
                let chain : Fin 67 := ⟨position.val.chain.val, chainBound⟩
                let previous : Fin 10 := ⟨position.val.step.val - 1, by omega⟩
                have previousRank : rank (upperChain base leafIndex chain previous) <
                    rank position := by
                  rw [upper_chain_rank]
                  have rankPosition : rank position = position.val.step.val := by
                    simp [rank, tagTwo, Nat.min_eq_left (by omega : position.val.step.val ≤ 9)]
                  rw [rankPosition]
                  change position.val.step.val - 1 < position.val.step.val
                  omega
                have values := same (upperChain base leafIndex chain previous) previousRank
                simp only [chainPayload, dif_neg bottom, dif_pos level,
                  dif_pos leaf, dif_pos chainBound, dif_pos stepBound,
                  dif_neg zero]
                exact congrArg (fun value : BitVec 256 => bytes (truncate value)) values
            · simp only [chainPayload, dif_neg bottom, dif_pos level,
                dif_pos leaf, dif_pos chainBound, dif_neg stepBound]
          · simp only [chainPayload, dif_neg bottom, dif_pos level,
              dif_pos leaf, dif_neg chainBound]
        · simp only [chainPayload, dif_neg bottom, dif_pos level, dif_neg leaf]
      · simp only [chainPayload, dif_neg bottom, dif_neg level]
  · by_cases tagThree : position.val.tag.val = 3
    · simp only [payload, if_neg tagTwo, if_pos tagThree]
      by_cases level : 10 ≤ position.val.level.val ∧ position.val.level.val < 160
      · by_cases fields : position.val.leaf.val = 0 ∧ position.val.chain.val = 0 ∧
            position.val.step.val = 0
        · let base : Fin 150 := ⟨position.val.level.val - 10, by omega⟩
          let leafIndex : BitVec 160 := BitVec.ofNat 160 position.val.tree.toNat
          have words : (fun chain : Fin 67 =>
              truncate (first (upperChain base leafIndex chain (endpointStep chain)))) =
              (fun chain : Fin 67 =>
              truncate (second (upperChain base leafIndex chain (endpointStep chain)))) := by
            funext chain
            have previousRank : rank (upperChain base leafIndex chain
                (endpointStep chain)) < rank position := by
              rw [upper_chain_rank]
              have rankPosition : rank position = 10 := by
                simp [rank, tagTwo, tagThree]
              rw [rankPosition]
              exact (endpointStep chain).isLt
            exact congrArg truncate
              (same (upperChain base leafIndex chain (endpointStep chain)) previousRank)
          simp only [leafPayload, dif_pos level, dif_pos fields]
          exact congrArg (fun words : Fin 67 → Digest =>
            (List.ofFn words).flatMap bytes) words
        · simp only [leafPayload, dif_pos level, dif_neg fields]
      · simp only [leafPayload, dif_neg level]
    · have tagFour : position.val.tag.val = 4 := by
        rcases position.property with two | three | four <;> omega
      by_cases small : position.val.level.val < 160
      · have childRank := node_children_rank position tagFour small
        have leftEq := same (nodeChildren position.val).1 childRank.1
        have rightEq := same (nodeChildren position.val).2 childRank.2
        simp only [payload, if_neg tagTwo, if_neg tagThree, if_pos small,
          nodePayload]
        rw [leftEq, rightEq]
      · simp only [payload, if_neg tagTwo, if_neg tagThree, if_neg small]

def graphInput (privateAnswers : PrivateAnswers) (labels : Labels)
    (position : Position) : Query :=
  position.input (payload privateAnswers labels position)

theorem graphInput_update_of_rank (privateAnswers : PrivateAnswers)
    (position later : Position) (ordered : rank position ≤ rank later)
    (labels : Labels) (answer : BitVec 256) :
    graphInput privateAnswers (Function.update labels later answer) position =
      graphInput privateAnswers labels position := by
  unfold graphInput
  apply congrArg position.input
  apply payload_congr
  intro child earlier
  have different : child ≠ later := by
    intro equal
    subst child
    omega
  exact Function.update_of_ne different _ _

end SigGolfCandidate.Hypertree.GroupedBalancedGraphCausality67

end

/-! Rank-ordered evaluation solves every grouped public graph equation for
the actual H function. This is the deterministic consistency boundary needed
before programming and probabilistic coupling. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphConsistency67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphOrder67 GroupedBalancedGraphCausality67
set_option maxHeartbeats 1000000

theorem readGraph_cons (hash : Hash) (privateAnswers : PrivateAnswers)
    (position : Position) (rest : List Position) (labels : GroupedBalancedSecurityGraph67.Labels) :
    evalWithAnswerFn hash (GroupedSecurityGraph.readGraph (payload privateAnswers)
      (position :: rest) labels) =
    evalWithAnswerFn hash (GroupedSecurityGraph.readGraph (payload privateAnswers) rest
      (Function.update labels position
        (hash (graphInput privateAnswers labels position)))) := rfl

theorem readGraph_input_preserved (hash : Hash)
    (privateAnswers : PrivateAnswers) (position : Position)
    (positions : List Position)
    (later : ∀ next ∈ positions, rank position ≤ rank next)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    graphInput privateAnswers
      (evalWithAnswerFn hash (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels))
      position = graphInput privateAnswers labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons next rest ih =>
      rw [readGraph_cons]
      exact (ih (fun item member => later item (List.mem_cons_of_mem _ member))
        (Function.update labels next (hash (graphInput privateAnswers labels next)))).trans
        (graphInput_update_of_rank privateAnswers position next
          (later next (by simp)) labels _)

theorem readGraph_label_preserved (hash : Hash)
    (privateAnswers : PrivateAnswers) (position : Position)
    (positions : List Position) (absent : position ∉ positions)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    evalWithAnswerFn hash
      (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels) position =
      labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons next rest ih =>
      have notNext : position ≠ next := fun equal => absent (by simp [equal])
      have notRest : position ∉ rest :=
        fun member => absent (List.mem_cons_of_mem _ member)
      rw [readGraph_cons]
      exact (ih notRest
        (Function.update labels next (hash (graphInput privateAnswers labels next)))).trans
        (Function.update_of_ne notNext _ _)

theorem readGraph_consistent (hash : Hash)
    (privateAnswers : PrivateAnswers) (positions : List Position)
    (distinct : positions.Nodup)
    (ordered : positions.Pairwise
      (fun first second => rank first ≤ rank second))
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    ∀ position ∈ positions,
      hash (graphInput privateAnswers
        (evalWithAnswerFn hash
          (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels)) position) =
      evalWithAnswerFn hash
        (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels) position := by
  induction positions generalizing labels with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨firstBefore, restOrdered⟩ := List.pairwise_cons.mp ordered
      intro position member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst position
        rw [readGraph_cons]
        calc
          hash (graphInput privateAnswers
              (evalWithAnswerFn hash
                (GroupedSecurityGraph.readGraph (payload privateAnswers) rest
                  (Function.update labels first (hash (graphInput privateAnswers labels first)))))
              first) =
              hash (graphInput privateAnswers
                (Function.update labels first (hash (graphInput privateAnswers labels first)))
                first) := by
                  exact congrArg hash (readGraph_input_preserved hash privateAnswers
                    first rest firstBefore _)
          _ = hash (graphInput privateAnswers labels first) := by
              exact congrArg hash (graphInput_update_of_rank privateAnswers
                first first le_rfl labels _)
          _ = (Function.update labels first (hash (graphInput privateAnswers labels first)))
              first := (Function.update_self first
                (hash (graphInput privateAnswers labels first)) labels).symm
          _ = evalWithAnswerFn hash
              (GroupedSecurityGraph.readGraph (payload privateAnswers) rest
                (Function.update labels first (hash (graphInput privateAnswers labels first))))
              first := (readGraph_label_preserved hash privateAnswers first rest notRest _).symm
      · rw [readGraph_cons]
        exact ih restDistinct restOrdered _ position member

theorem complete_readGraph_consistent (hash : Hash)
    (privateAnswers : PrivateAnswers) (labels : GroupedBalancedSecurityGraph67.Labels)
    (position : Position) :
    hash (graphInput privateAnswers
      (evalWithAnswerFn hash
        (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels)) position) =
      evalWithAnswerFn hash
        (GroupedSecurityGraph.readGraph (payload privateAnswers) positions labels) position :=
  readGraph_consistent hash privateAnswers positions
    positions_nodup positions_ordered labels position (positions_complete position)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphConsistency67
