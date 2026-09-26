import SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomMerkleContact67
import SigGolfCandidate.Hypertree.GroupedBalancedWotsExtraction67

/-! Every direct67 WOTS leaf or chain collision is a concrete public output
contact at the exact verifier query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsContact67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperTree67
open GroupedBalancedWotsExtraction67 SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem leaf_collision_contact
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (base : Fin 150) (leaf : BitVec 160)
    (message : Reference.Digest)
    (values : ChainMixed → Reference.Digest)
    (bad : LeafCollision (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat message values) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) := by
  rcases bad with leafCollision | chainCollision
  · have endpoints :
        (fun chain : ChainMixed => endpoint
          (programmedGrouped residual secretKey labels) secretKey
          (base.val + 10) leaf.toNat chain) =
        (fun chain : ChainMixed => truncate
          (labels (upperChain base leaf chain (endpointStep chain)))) := by
      funext chain
      exact GroupedBalancedGraphProgrammedLeaf67.programmed_upper_endpoint
        residual secretKey labels base leaf chain
    have expectedPayload :
        ((List.ofFn (endpoint (programmedGrouped residual secretKey labels)
          secretKey (base.val + 10) leaf.toNat)).flatMap bytes) =
        ((List.ofFn (fun chain : ChainMixed => truncate
          (labels (upperChain base leaf chain (endpointStep chain))))).flatMap bytes) := by
      rw [← endpoints]
    rw [expectedPayload] at leafCollision
    refine ⟨(upperLeaf base leaf).input
      ((List.ofFn (fun chain => walk
        (chainHash (programmedGrouped residual secretKey labels)
          (base.val + 10) leaf.toNat chain)
        (digit message chain).val
        (maxDigit chain - (digit message chain).val)
        (values chain))).flatMap bytes), ?_⟩
    exact GroupedBalancedGraphMonitorCollisionBridge67.upper_leaf_collision_outputHit
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      base leaf _ leafCollision
  · rcases chainCollision with ⟨chain, offset, offsetBound, collision⟩
    let step := (digit message chain).val + offset
    have digitBound := GroupedBalancedChecksum67.digit_le_max message chain
    change (digit message chain).val ≤ maxDigit chain at digitBound
    change offset < maxDigit chain - (digit message chain).val at offsetBound
    have stepBound : step < maxDigit chain := by
      dsimp [step]
      omega
    have stepTen : step < 10 := lt_of_lt_of_le stepBound
      (GroupedBalancedSecurityGraph67.max_digit_le_ten chain)
    by_cases zero : step = 0
    · have stepEq : (digit message chain).val + offset = 0 := by
        simpa only [step] using zero
      have canonical :
          walk (chainHash (programmedGrouped residual secretKey labels)
            (base.val + 10) leaf.toNat chain) 0 0
            (secret (programmedGrouped residual secretKey labels)
              secretKey (base.val + 10) leaf.toNat chain) =
          secret residual secretKey (base.val + 10) leaf.toNat chain := by
        simpa only [walk] using
          GroupedBalancedGraphProgrammedReference67.programmed_upper_secret
            residual secretKey labels base leaf chain
      rw [stepEq, canonical] at collision
      refine ⟨(upperChain base leaf chain 0).input
        (bytes (walk
          (chainHash (programmedGrouped residual secretKey labels)
            (base.val + 10) leaf.toNat chain)
            (digit message chain).val offset (values chain))), ?_⟩
      exact GroupedBalancedGraphMonitorCollisionBridge67.upper_zero_collision_outputHit
        table residual secretKey labels labelsMatch bottomMatch
        sourceMatch base leaf chain _ collision
    · let previous := step - 1
      have stepEq : (digit message chain).val + offset = previous + 1 := by
        dsimp [step, previous] at *
        omega
      have previousBound : previous < 9 := by
        dsimp [previous] at *
        omega
      let previousFin : Fin 9 := ⟨previous, previousBound⟩
      have canonical :
          walk (chainHash (programmedGrouped residual secretKey labels)
            (base.val + 10) leaf.toNat chain) 0 (previous + 1)
            (secret (programmedGrouped residual secretKey labels)
              secretKey (base.val + 10) leaf.toNat chain) =
          truncate (labels
            (upperChain base leaf chain ⟨previous, by omega⟩)) := by
        simpa only [Nat.succ_eq_add_one] using
          GroupedBalancedGraphProgrammedLeaf67.programmed_upper_walk
            residual secretKey labels base leaf chain previous (by omega)
      rw [stepEq, canonical] at collision
      refine ⟨(upperChain base leaf chain
          ⟨previous + 1, by omega⟩).input
        (bytes (walk
          (chainHash (programmedGrouped residual secretKey labels)
            (base.val + 10) leaf.toNat chain)
            (digit message chain).val offset (values chain))), ?_⟩
      exact GroupedBalancedGraphMonitorCollisionBridge67.upper_step_collision_outputHit
        table residual secretKey labels labelsMatch bottomMatch
        sourceMatch base leaf chain previousFin _ collision

end SigGolfCandidate.Hypertree.GroupedBalancedGraphWotsContact67
