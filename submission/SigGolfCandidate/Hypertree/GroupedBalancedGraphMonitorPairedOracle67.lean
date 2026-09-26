import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetupBound67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedReference67


/-! Canonical graph payloads observe only the 67 used chain-source halves.
The high half of the final, 34th paired secret answer is irrelevant. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPayloadExt67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67
open GroupedBalancedGraphPassive67

theorem chainPayload_ext (first second : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : ∀ index, first.bottom index = second.bottom index)
    (upper : ∀ base leaf chain,
      chainSource first base leaf chain = chainSource second base leaf chain)
    (address : SecurityGraph.Address) :
    chainPayload first labels address = chainPayload second labels address := by
  unfold chainPayload
  split_ifs with bottomCase level leaf chainBound stepBound zero
  · exact congrArg (fun answer => bytes (truncate answer)) (bottom _)
  · exact congrArg bytes (upper _ _ _)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem payload_ext (first second : PrivateAnswers)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : ∀ index, first.bottom index = second.bottom index)
    (upper : ∀ base leaf chain,
      chainSource first base leaf chain = chainSource second base leaf chain)
    (position : Position) :
    payload first labels position = payload second labels position := by
  by_cases chain : position.val.tag.val = 2
  · simp only [payload, if_pos chain]
    exact chainPayload_ext first second labels bottom upper position.val
  · simp only [payload, if_neg chain]

theorem payload_fromPairs (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : GroupedBalancedGraphMonitorFactors67.BottomTable)
    (pairs : GroupedBalancedGlobalPaired67.PairTable)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (position : Position) :
    payload
      (GroupedBalancedGraphMonitorTable67.privateOf
        (GroupedBalancedGraphMonitorFactors67.fromPairs labels bottom pairs ghosts))
      labels position =
    payload ⟨bottom, fun base leaf pair => pairs (base, leaf) pair⟩
      labels position := by
  apply payload_ext
  · intro index
    exact GroupedBalancedGraphMonitorTable67.bottom_fromPairs
      labels bottom pairs ghosts index
  · intro base leaf chain
    exact GroupedBalancedGraphMonitorTable67.upper_source_fromPairs
      labels bottom pairs ghosts base leaf chain

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPayloadExt67



/-! Transfer the adaptive public contact bound from a uniform monitor table
to the actual independent 34-pair private source distribution, padded with
one unused ghost half per upper address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedBound67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorFactors67
open GroupedBalancedGraphMonitorCompileCoupling67
open GroupedBalancedGraphMonitorSetup67
open GroupedBalancedGraphMonitorSetupBound67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

theorem paired_keyed_contact_le {α : Type}
    (program : Reference.Digest → OracleComp World α)
    (remaining : Nat) :
    Pr[= none | do
      let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
      let bottom ← $ᵗ BottomTable
      let pairs ← $ᵗ GroupedBalancedGlobalPaired67.PairTable
      let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
      let table := fromPairs labels bottom pairs ghosts
      execute table (program (rootPublic table)) remaining
        (cache table, ∅)] ≤
      (2 * remaining : Nat) / (2 : ENNReal) ^ 128 := by
  have same := uniform_fromPairs_bind (fun table : PointTable =>
    execute table (program (rootPublic table)) remaining (cache table, ∅))
  rw [probOutput_def, same, ← probOutput_def]
  exact planted_keyed_contact_le program remaining

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedBound67


/-! The ghost-padded uniform monitor table has the same canonical public
random-oracle queries as the actual 34-pair private-source table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedOracle67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorFactors67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedGraphMonitorPayloadExt67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

def actualPrivate (bottom : BottomTable)
    (pairs : GroupedBalancedGlobalPaired67.PairTable) :
    GroupedBalancedGraphPayload67.PrivateAnswers :=
  ⟨bottom, fun base leaf pair => pairs (base, leaf) pair⟩

theorem graphInput_fromPairs
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable)
    (pairs : GroupedBalancedGlobalPaired67.PairTable)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (position : Position) :
    GroupedBalancedGraphCausality67.graphInput
      (privateOf (fromPairs labels bottom pairs ghosts))
      (labelsOf (fromPairs labels bottom pairs ghosts)) position =
    GroupedBalancedGraphCausality67.graphInput
      (actualPrivate bottom pairs) labels position := by
  rw [labelsOf_fromPairs]
  exact congrArg position.input
    (payload_fromPairs labels bottom pairs ghosts position)

theorem canonical_fromPairs
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable)
    (pairs : GroupedBalancedGlobalPaired67.PairTable)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable)
    (query : Query) :
    GroupedBalancedGraphOracle67.canonical
      (privateOf (fromPairs labels bottom pairs ghosts))
      (labelsOf (fromPairs labels bottom pairs ghosts)) query =
    GroupedBalancedGraphOracle67.canonical
      (actualPrivate bottom pairs) labels query := by
  unfold GroupedBalancedGraphOracle67.canonical
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none => rfl
  | some position =>
      change (if query = GroupedBalancedGraphCausality67.graphInput
          (privateOf (fromPairs labels bottom pairs ghosts))
          (labelsOf (fromPairs labels bottom pairs ghosts)) position
        then some (labelsOf (fromPairs labels bottom pairs ghosts) position)
        else none) =
        (if query = GroupedBalancedGraphCausality67.graphInput
          (actualPrivate bottom pairs) labels position
        then some (labels position) else none)
      rw [graphInput_fromPairs, labelsOf_fromPairs]

theorem publicOracle_fromPairs
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable)
    (pairs : GroupedBalancedGlobalPaired67.PairTable)
    (ghosts : GroupedBalancedGlobalPaired67.GhostTable) :
    GroupedBalancedGraphOracle67.publicOracle
      (privateOf (fromPairs labels bottom pairs ghosts))
      (labelsOf (fromPairs labels bottom pairs ghosts)) =
    GroupedBalancedGraphOracle67.publicOracle
      (actualPrivate bottom pairs) labels := by
  funext query
  simp only [GroupedBalancedGraphOracle67.publicOracle,
    canonical_fromPairs]

/-- A private source match only needs the bottom answers and the 67 used
128-bit chain-source halves. The dormant 68th paired half is irrelevant to
every programmed public query. -/
theorem programmedGrouped_lookup (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (table : PointTable)
    (labelsMatch : labels = labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (privateOf table) base leaf chain)
    (query : Query) :
    GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey labels query =
      match GroupedBalancedGraphOracle67.canonical
        (privateOf table) (labelsOf table) query with
      | some answer => answer
      | none => residual query := by
  subst labels
  have payloadEq :
      GroupedBalancedGraphPayload67.payload
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        (labelsOf table) =
      GroupedBalancedGraphPayload67.payload (privateOf table)
        (labelsOf table) := by
    funext position
    exact payload_ext _ _ _ bottomMatch sourceMatch position
  change GroupedBalancedGraphProgramming67.programmed
    (GroupedBalancedGraphPayload67.payload
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
      (labelsOf table)) (labelsOf table) residual query = _
  rw [payloadEq]
  exact GroupedBalancedGraphOracle67.programmed_hash
    (privateOf table) (labelsOf table) residual query

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedOracle67
