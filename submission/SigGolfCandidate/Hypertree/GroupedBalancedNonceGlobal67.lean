import SigGolfCandidate.Hypertree.GroupedBalancedNonceCompilerErase67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointClassTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPairedGlobal67


/-! The secret-key query-class counter commutes with lazy nonce
instantiation. Only public hash actions charge that class. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceClassView67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedNonceView67
open GroupedBalancedGraphIndexJointClassTrace67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

noncomputable def annotate {α : Type} : NView α → Nat → NView (α × Nat)
  | .done value, secret => .done (value, secret)
  | .coin n next, secret => .coin n (fun answer =>
      annotate (next answer) secret)
  | .sign index next, secret => .sign index (fun answer =>
      annotate (next answer) secret)
  | .privateHash input outside next, secret =>
      .privateHash input outside (fun answer =>
        annotate (next answer) secret)
  | .hash input next, secret =>
      .hash input (fun answer =>
        annotate (next answer) (secret + secretCharge input))
  | .nonce message next, secret => .nonce message (fun answer =>
      annotate (next answer) secret)

theorem instantiate_annotate {α : Type}
    (nonces : Message → BitVec 256) (view : NView α)
    (secret : Nat) :
    instantiate nonces (annotate view secret) =
      GroupedBalancedGraphIndexJointClassTrace67.annotate
        (instantiate nonces view) secret := by
  induction view generalizing secret with
  | done value => rfl
  | coin n next ih =>
      simp only [annotate, instantiate,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | sign n next ih =>
      simp only [annotate, instantiate,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | privateHash n outside next ih =>
      simp only [annotate, instantiate,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer => ih answer secret)
  | hash input next ih =>
      simp only [annotate, instantiate,
        GroupedBalancedGraphIndexJointClassTrace67.annotate]
      exact congrArg _ (funext fun answer =>
        ih answer (secret + secretCharge input))
  | nonce message next ih =>
      exact ih (nonces message) secret

#print axioms instantiate_annotate

end SigGolfCandidate.Hypertree.GroupedBalancedNonceClassView67


/-! One nonce-independent passive program for the complete stopped direct67
graph/H5 experiment. It samples the public point table before the attacker
view and requests randomizers only at signing actions. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedNonceView67
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceJointCompiler67
open GroupedBalancedNonceClassView67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
open scoped Classical

def unmarked {α β : Type} (program : ProbComp α)
    (next : α → Program β) : Program β :=
  OracleComp.construct next (fun n _ continuation => .coin n continuation)
    program

theorem erase_unmarked {α β : Type}
    (nonces : Message → BitVec 256) (program : ProbComp α)
    (next : α → Program β) :
    GroupedBalancedNonceProgram67.erase nonces (unmarked program next) =
      GroupedBalancedIndexLabeledLift67.unmarked program
        (fun value => GroupedBalancedNonceProgram67.erase nonces
          (next value)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind n child ih =>
      change GroupedBalancedNonceProgram67.erase nonces
        (.coin n (fun answer => unmarked (child answer) next)) =
        GroupedBalancedIndexLabeledProgram67.Program.coin n
          (fun answer => GroupedBalancedIndexLabeledLift67.unmarked
            (child answer)
            (fun value => GroupedBalancedNonceProgram67.erase nonces
              (next value)))
      simp only [GroupedBalancedNonceProgram67.erase]
      exact congrArg _ (funext fun answer => ih answer)

noncomputable def global {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) : Program
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option α × List GroupedBalancedGameQueryTrace67.Action) × Nat)) :=
  unmarked ($ᵗ PointTable) (fun table =>
    start table
      (fun cache =>
        GroupedBalancedNonceClassView67.annotate
          (GroupedBalancedNonceView67.cutoff cache (interaction cache)
            budget) 0) budget)

theorem erase_global {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable)
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    GroupedBalancedNonceProgram67.erase
      (fun message => answers (.randomizer message))
      (global interaction budget) =
    GroupedBalancedIndexLabeledGlobal67.global
      (fun cache =>
        GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedPlantedEagerGraphProjection67.viewOf
            answers interaction budget cache) 0) budget := by
  rw [global, erase_unmarked]
  change _ = GroupedBalancedIndexLabeledLift67.unmarked
    ($ᵗ PointTable)
    (fun table => GroupedBalancedIndexLabeledJoint67.start table
      (fun cache =>
        GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedPlantedEagerGraphProjection67.viewOf
            answers interaction budget cache) 0) budget)
  congr 1
  funext table
  rw [GroupedBalancedNonceCompilerErase67.erase_start]
  congr 1
  funext cache
  rw [GroupedBalancedNonceClassView67.instantiate_annotate,
    GroupedBalancedNonceView67.instantiate_cutoff]
  rfl

#print axioms erase_unmarked
#print axioms erase_global

end SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobal67
