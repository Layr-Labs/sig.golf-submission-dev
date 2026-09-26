import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCredit67

/-! Leaf and node payloads depend only on the terminal or metadata children
that `publicStep` discloses. Their other point-table entries are irrelevant. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorRequired67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67 GroupedBalancedGraphPayload67
open GroupedBalancedGraphMonitorOracle67

theorem revealCache_mem (table : PointTable) (points : List Point)
    (exposed : QueryCache PointSpec) (point : Point) (member : point ∈ points) :
    revealCache table points exposed point = some (table point) := by
  have preserves (points : List Point) (cache : QueryCache PointSpec)
      (known : cache point = some (table point)) :
      revealCache table points cache point = some (table point) := by
    induction points generalizing cache with
    | nil => exact known
    | cons other rest ih =>
        apply ih
        by_cases same : point = other
        · subst other
          simp
        · simpa only [QueryCache.cacheQuery_of_ne _ _ same] using known
  induction points generalizing exposed with
  | nil => simp at member
  | cons other rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst other
        exact preserves rest _ (by simp)
      · exact ih _ later

theorem knownTable_mem (table : PointTable) (points : List Point)
    (exposed : QueryCache PointSpec) (point : Point) (member : point ∈ points) :
    knownTable (revealCache table points exposed) point = table point := by
  simp only [knownTable, revealCache_mem table points exposed point member,
    Option.getD_some]

theorem required_input (table : PointTable) (exposed : QueryCache PointSpec)
    (position : Position) (nonchain : position.val.tag.val ≠ 2)
    (ready : ∀ point ∈ required position, exposed point = some (table point)) :
    payload (GroupedBalancedGraphMonitorTable67.privateOf (knownTable exposed))
      (GroupedBalancedGraphMonitorTable67.labelsOf (knownTable exposed)) position =
    payload (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
  by_cases tagThree : position.val.tag.val = 3
  · simp only [payload, if_neg nonchain, if_pos tagThree]
    by_cases level : 10 ≤ position.val.level.val ∧ position.val.level.val < 160
    · by_cases fields : position.val.leaf.val = 0 ∧
          position.val.chain.val = 0 ∧ position.val.step.val = 0
      · let base : Fin 150 := ⟨position.val.level.val - 10, by omega⟩
        let leaf : BitVec 160 := BitVec.ofNat 160 position.val.tree.toNat
        have words : (fun chain : Fin 67 => truncate
            (GroupedBalancedGraphMonitorTable67.labelsOf (knownTable exposed)
              (upperChain base leaf chain (endpointStep chain)))) =
            (fun chain : Fin 67 => truncate
              (GroupedBalancedGraphMonitorTable67.labelsOf table
                (upperChain base leaf chain (endpointStep chain)))) := by
          funext chain
          have member : (Sum.inl (upperChain base leaf chain (endpointStep chain))) ∈
              required position := by
            simp only [required, if_pos tagThree, dif_pos level]
            exact List.mem_ofFn.mpr ⟨chain, rfl⟩
          exact congrArg truncate (by
            simp only [GroupedBalancedGraphMonitorTable67.labelsOf, knownTable,
              ready _ member, Option.getD_some])
        simp only [leafPayload, dif_pos level, dif_pos fields]
        exact congrArg (fun words : Fin 67 → Digest =>
          (List.ofFn words).flatMap bytes) words
      · simp only [leafPayload, dif_pos level, dif_neg fields]
    · simp only [leafPayload, dif_neg level]
  · by_cases small : position.val.level.val < 160
    · have tagFour : position.val.tag.val = 4 := by
        rcases position.property with two | three | four <;> omega
      have leftMember : Sum.inl (nodeChildren position.val).1 ∈
          required position := by
        simp [required, tagThree, tagFour, small]
      have rightMember : Sum.inl (nodeChildren position.val).2 ∈
          required position := by
        simp [required, tagThree, tagFour, small]
      have left := ready _ leftMember
      have right := ready _ rightMember
      simp only [payload, if_neg nonchain, if_neg tagThree, if_pos small,
        nodePayload, GroupedBalancedGraphMonitorTable67.labelsOf, knownTable,
        left, right, Option.getD_some]
    · simp only [payload, if_neg nonchain, if_neg tagThree, if_neg small]

theorem required_after_reveal (table : PointTable)
    (exposed : QueryCache PointSpec) (position : Position)
    (nonchain : position.val.tag.val ≠ 2) :
    payload (GroupedBalancedGraphMonitorTable67.privateOf
      (knownTable (revealCache table (required position) exposed)))
      (GroupedBalancedGraphMonitorTable67.labelsOf
        (knownTable (revealCache table (required position) exposed))) position =
    payload (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
  apply required_input table _ position nonchain
  intro point member
  exact revealCache_mem table (required position) exposed point member

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorRequired67
