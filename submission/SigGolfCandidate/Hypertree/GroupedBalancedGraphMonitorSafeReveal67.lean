import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67

/-! Leaf endpoints and Merkle children required by the direct 67-chain
monitor lie on or beyond the canonical exposure frontier. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSafeReveal67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorOracle67
set_option maxRecDepth 8192

theorem safe_public (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) (position : Position)
    (safe : position.val.tag.val ≠ 2 ∨ position.val.level.val = 0) :
    Authorized labels signedBottom (.inl position) := by
  intro base leaf chain step same
  have tagEq := congrArg (fun p : Position => p.val.tag.val) same
  have levelEq := congrArg (fun p : Position => p.val.level.val) same
  rcases safe with tag | level
  · change position.val.tag.val = 2 at tagEq
    exact False.elim (tag tagEq)
  · have bound := base.isLt
    simp only [upperChain] at levelEq
    omega

theorem safe_node_child (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160))
    (address : SecurityGraph.Address) (side : Bool) :
    Authorized labels signedBottom
      (.inl (if side then (GroupedBalancedGraphPayload67.nodeChildren address).1
        else (GroupedBalancedGraphPayload67.nodeChildren address).2)) := by
  apply safe_public
  simp only [GroupedBalancedGraphPayload67.nodeChildren]
  split_ifs <;> simp [bottomLeaf, bottomNode, upperLeaf, upperNode]

theorem required_authorized (labels : GroupedBalancedSecurityGraph67.Labels)
    (signedBottom : Finset (BitVec 160)) (position : Position)
    (point : Point) (member : point ∈ required position) :
    Authorized labels signedBottom point := by
  by_cases tagThree : position.val.tag.val = 3
  · by_cases level : 10 ≤ position.val.level.val ∧
        position.val.level.val < 160
    · simp only [required, if_pos tagThree, dif_pos level] at member
      obtain ⟨chain, same⟩ := List.mem_ofFn.mp member
      subst point
      exact upper_endpoint_authorized labels signedBottom
        ⟨position.val.level.val - 10, by omega⟩
        (BitVec.ofNat 160 position.val.tree.toNat) chain
    · simp [required, tagThree, level] at member
  · by_cases node : position.val.tag.val = 4 ∧
        position.val.level.val < 160
    · simp only [required, if_neg tagThree, if_pos node,
        List.mem_cons] at member
      rcases member with same | same
      · rw [same]
        simpa using safe_node_child labels signedBottom position.val true
      · simp only [List.not_mem_nil, or_false] at same
        rw [same]
        simpa using safe_node_child labels signedBottom position.val false
    · simp [required, tagThree, node] at member

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSafeReveal67
