import SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointPresample67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorTable67

/-! The joint RO sampler's private H1 values and public labels align with the
uniform point table used by the direct67 organizer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointTable67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedPrivateDerivation67 GroupedBalancedPrivateFactors67
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorFactors67 GroupedBalancedGlobalPaired67
open GroupedBalancedSecurityJointPresample67
open scoped Classical
set_option maxRecDepth 8192

def tableOf (answers : PrivateTable) (labels : Labels)
    (ghosts : GhostTable) : PointTable :=
  fromPairs labels
    (fun index => answers (.bottom index))
    (fun address pair => answers (.upper address.1 address.2 pair))
    ghosts

@[simp] theorem labelsOf_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable) :
    GroupedBalancedGraphMonitorTable67.labelsOf
      (tableOf answers labels ghosts) = labels := by
  exact GroupedBalancedGraphMonitorTable67.labelsOf_fromPairs labels _ _ ghosts

theorem bottom_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable) (index : BitVec 160) :
    (GroupedBalancedGraphMonitorTable67.privateOf
      (tableOf answers labels ghosts)).bottom index =
    (privateOfAnswers answers).bottom index := by
  rfl

theorem source_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedGraphPayload67.chainSource
      (GroupedBalancedGraphMonitorTable67.privateOf
        (tableOf answers labels ghosts)) base leaf chain =
    GroupedBalancedGraphPayload67.chainSource
      (privateOfAnswers answers) base leaf chain := by
  rw [GroupedBalancedGraphMonitorTable67.upper_source]
  simpa only [tableOf, privateOfAnswers] using
    (GroupedBalancedGraphMonitorFactors67.upper_secret_value labels
    (fun index => answers (.bottom index))
    (fun address pair => answers (.upper address.1 address.2 pair))
    ghosts base leaf chain)

theorem payload_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable) (position : Position) :
    GroupedBalancedGraphPayload67.payload
      (privateOfAnswers answers) labels position =
    GroupedBalancedGraphPayload67.payload
      (GroupedBalancedGraphMonitorTable67.privateOf
        (tableOf answers labels ghosts)) labels position := by
  simp only [GroupedBalancedGraphPayload67.payload,
    GroupedBalancedGraphPayload67.chainPayload,
    bottom_tableOf, source_tableOf]

theorem graph_input_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable) (position : Position) :
    GroupedBalancedGraphCausality67.graphInput
      (privateOfAnswers answers) labels position =
    GroupedBalancedGraphCausality67.graphInput
      (GroupedBalancedGraphMonitorTable67.privateOf
        (tableOf answers labels ghosts)) labels position := by
  exact congrArg position.input (payload_tableOf answers labels ghosts position)

theorem graph_cache_tableOf (answers : PrivateTable)
    (labels : Labels) (ghosts : GhostTable)
    (positions : List Position) (cache : QueryCache HashSpec) :
    GroupedBalancedGraphSampling67.graphCache
      (privateOfAnswers answers) positions labels cache =
    GroupedBalancedGraphSampling67.graphCache
      (GroupedBalancedGraphMonitorTable67.privateOf
        (tableOf answers labels ghosts)) positions labels cache := by
  induction positions generalizing cache with
  | nil => rfl
  | cons position rest ih =>
      simp only [GroupedBalancedGraphSampling67.graphCache]
      rw [graph_input_tableOf answers labels ghosts position]
      exact ih _

/-- The private source table, public labels, and unused upper-source padding
factor into the organizer's uniform point table and an independent nonce
table. The nonce table remains available for honest signing. -/
theorem uniform_table_and_nonce {α : Type}
    (next : PointTable → NonceTable → ProbComp α) :
    𝒮[do
      let answers ← $ᵗ PrivateTable
      let labels ← $ᵗ Labels
      let ghosts ← $ᵗ GhostTable
      next (tableOf answers labels ghosts)
        (fun message => answers (.randomizer message))] =
    𝒮[do
      let table ← $ᵗ PointTable
      let nonces ← $ᵗ NonceTable
      next table nonces] := by
  calc
    _ = 𝒮[do
      let labels ← $ᵗ Labels
      let answers ← $ᵗ PrivateTable
      let ghosts ← $ᵗ GhostTable
      next (tableOf answers labels ghosts)
        (fun message => answers (.randomizer message))] := by
          exact evalSPMF_bind_bind_swap _ _ _
    _ = 𝒮[do
      let labels ← $ᵗ Labels
      let bottom ← $ᵗ GroupedBalancedPrivateFactors67.BottomTable
      let pairs ← $ᵗ UpperTable
      let nonces ← $ᵗ NonceTable
      let ghosts ← $ᵗ GhostTable
      next (fromPairs labels bottom pairs ghosts) nonces] := by
          apply evalSPMF_bind_congr
          intro labels _
          simpa only [tableOf, GroupedBalancedPrivateFactors67.factor,
            bind_assoc, pure_bind] using
            (GroupedBalancedPrivateFactors67.independent_bind
              (fun factors => do
                let ghosts ← $ᵗ GhostTable
                next (fromPairs labels factors.1 factors.2.1 ghosts)
                  factors.2.2))
    _ = 𝒮[do
      let labels ← $ᵗ Labels
      let bottom ← $ᵗ GroupedBalancedPrivateFactors67.BottomTable
      let pairs ← $ᵗ UpperTable
      let ghosts ← $ᵗ GhostTable
      let nonces ← $ᵗ NonceTable
      next (fromPairs labels bottom pairs ghosts) nonces] := by
          apply evalSPMF_bind_congr
          intro labels _
          apply evalSPMF_bind_congr
          intro bottom _
          apply evalSPMF_bind_congr
          intro pairs _
          exact evalSPMF_bind_bind_swap _ _ _
    _ = _ := GroupedBalancedGraphMonitorFactors67.uniform_fromPairs_bind
      (fun table => do
        let nonces ← $ᵗ NonceTable
        next table nonces)

theorem uniform_table {α : Type} (next : PointTable → ProbComp α) :
    𝒮[do
      let answers ← $ᵗ PrivateTable
      let labels ← $ᵗ Labels
      let ghosts ← $ᵗ GhostTable
      next (tableOf answers labels ghosts)] =
    𝒮[do let table ← $ᵗ PointTable; next table] := by
  calc
    _ = 𝒮[do
      let table ← $ᵗ PointTable
      let _ ← $ᵗ NonceTable
      next table] := uniform_table_and_nonce (fun table _ => next table)
    _ = _ := by
      apply evalSPMF_bind_congr
      intro table _
      apply evalSPMF_ext
      intro output
      rw [probOutput_bind_const]
      simp

#print axioms source_tableOf
#print axioms graph_input_tableOf
#print axioms graph_cache_tableOf
#print axioms uniform_table_and_nonce
#print axioms uniform_table

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointTable67
