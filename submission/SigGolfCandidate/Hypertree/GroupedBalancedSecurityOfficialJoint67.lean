import SigGolfCandidate.Hypertree.GroupedBalancedSecurityJointInteraction67

/-! The submitted security experiment has the exact graph-view distribution
after jointly sampling private H1 sources and public graph labels. Honest
signing randomizers remain lazy in the shared random oracle. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialJoint67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedSecurityJointPresample67
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedSecurityJointInteraction67
open GroupedBalancedSecurityJointContext67
open GroupedBalancedPrivateFactors67 GroupedBalancedSecurityGraph67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem ignore_ghost_sample {α : Type} (program : ProbComp α) :
    𝒮[program] = 𝒮[do
      let _ ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
      program] := by
  apply evalSPMF_ext
  intro output
  rw [probOutput_bind_const]
  simp

/-- Distributional identity for the actual submitted experiment. The full
`AttackResult`, including its exact bytecode hash-call count, is retained. -/
theorem official_joint_semantic
    (adversary : Adversary submission.sizes) (rounds : Nat) :
    𝒮[submission.securityExperiment adversary rounds] =
    𝒮[do
      let secretKey ← sampleSecretKey
      let answers ← $ᵗ PrivateTable
      let labels ← $ᵗ Labels
      let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
      SecurityGraphHidden.observe
        (gameWith (semanticInterface answers labels ghosts)
          adversary rounds secretKey)
        (jointCache secretKey answers labels)] := by
  rw [GroupedBalancedSecurityJointInteraction67.official_game]
  apply evalSPMF_bind_congr
  intro secretKey _
  calc
    𝒮[SecurityGraphHidden.observe
      (gameWith actualInterface adversary rounds secretKey) ∅] =
        𝒮[do
          let answers ← $ᵗ PrivateTable
          let labels ← $ᵗ Labels
          SecurityGraphHidden.observe
            (gameWith actualInterface adversary rounds secretKey)
            (jointCache secretKey answers labels)] := by
          simpa only [jointCache] using
            joint_source_presampling secretKey
              (gameWith actualInterface adversary rounds secretKey)
              (fun _ => 0)
    _ = 𝒮[do
          let answers ← $ᵗ PrivateTable
          let labels ← $ᵗ Labels
          let ghosts ← $ᵗ GroupedBalancedGlobalPaired67.GhostTable
          SecurityGraphHidden.observe
            (gameWith actualInterface adversary rounds secretKey)
            (jointCache secretKey answers labels)] := by
          apply evalSPMF_bind_congr
          intro answers _
          apply evalSPMF_bind_congr
          intro labels _
          exact ignore_ghost_sample _
    _ = _ := by
          apply evalSPMF_bind_congr
          intro answers _
          apply evalSPMF_bind_congr
          intro labels _
          apply evalSPMF_bind_congr
          intro ghosts _
          exact game_equivalent secretKey answers labels ghosts
            adversary rounds

#print axioms official_joint_semantic

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialJoint67
