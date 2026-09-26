import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointMarkHelpers67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointBound67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointLifetime67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointOrganizerBound67. -/
section
/-! A private View step costs at most one marked draw. The organizer's two
private steps per sign therefore fit the doubled lifetime monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointLifetime67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointViewBudget67
open GroupedBalancedGraphIndexJointMarkHelpers67
open GroupedBalancedGraphIndexMarks67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 30000
open scoped Classical

theorem done_step {α : Type} (table : PointTable) (value : α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent privateRemaining limit : Nat)
    (bounded : spent + privateRemaining ≤ limit) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (.done value) remaining state graphCalls
        signedMessages bad tests) := by
  change spent ≤ limit
  omega

theorem coin_step {α : Type} (table : PointTable)
    (n : Nat) (next : Fin (n + 1) → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent limit : Nat)
    (ih : ∀ answer,
      MarkedCredit (fun _ : JointOutcome α => limit) spent
        (compile table (next answer) remaining state graphCalls
          signedMessages bad tests)) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (.coin n next) remaining state graphCalls
        signedMessages bad tests) := by
  change ∀ answer : Fin (n + 1),
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (next answer) remaining state graphCalls
        signedMessages bad tests)
  exact ih

attribute [local irreducible] MarkedCredit
attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile

theorem sign_step {α : Type} (table : PointTable)
    (index : BitVec 160) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent privateRemaining limit : Nat)
    (budget : ∀ answer, PrivateBudget privateRemaining (next answer))
    (bounded : spent + privateRemaining ≤ limit)
    (ih : ∀ answer updated,
      PrivateBudget privateRemaining (next answer) →
      MarkedCredit (fun _ : JointOutcome α => limit) spent
        (compile table (next answer) remaining updated graphCalls
          signedMessages bad tests)) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (.sign index next) remaining state graphCalls
        signedMessages bad tests) := by
  rw [GroupedBalancedGraphIndexJoint67.compile]
  exact ih _ _ (budget _)

theorem private_step {α : Type} (table : PointTable)
    (input : Query) (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent privateRemaining limit : Nat)
    (budget : 0 < privateRemaining ∧ ∀ answer,
      PrivateBudget (privateRemaining - 1) (next answer))
    (bounded : spent + privateRemaining ≤ limit)
    (ih : ∀ answer updated messages,
      PrivateBudget (privateRemaining - 1) (next answer) →
      spent + 1 + (privateRemaining - 1) ≤ limit →
      MarkedCredit (fun _ : JointOutcome α => limit) (spent + 1)
        (compile table (next answer) remaining updated graphCalls
          messages bad tests)) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (.privateHash input outside next) remaining state
        graphCalls signedMessages bad tests) := by
  rw [GroupedBalancedGraphIndexJoint67.compile]
  apply private_hash_step_credit
  intro answer updated messages
  exact ih answer updated messages (budget.2 answer) (by omega)

theorem hash_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (spent privateRemaining limit : Nat)
    (budget : ∀ answer, PrivateBudget privateRemaining (next answer))
    (bounded : spent + privateRemaining ≤ limit)
    (ih : ∀ answer updated graphCalls bad tests,
      PrivateBudget privateRemaining (next answer) →
      MarkedCredit (fun _ : JointOutcome α => limit) spent
        (compile table (next answer) (remaining - 1) updated
          graphCalls signedMessages bad tests)) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table (.hash input next) remaining state graphCalls
        signedMessages bad tests) := by
  cases remaining with
  | zero =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      simp only [MarkedCredit]
      omega
  | succ remaining =>
      rw [GroupedBalancedGraphIndexJoint67.compile]
      apply public_hash_step_credit
      intro answer updated graphCalls bad tests
      exact ih answer updated graphCalls bad tests (budget answer)

theorem compile_budget {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (spent privateRemaining limit : Nat)
    (budget : PrivateBudget privateRemaining view)
    (bounded : spent + privateRemaining ≤ limit) :
    MarkedCredit (fun _ : JointOutcome α => limit) spent
      (compile table view remaining state graphCalls
        signedMessages bad tests) := by
  induction view generalizing remaining state graphCalls signedMessages
      bad tests spent privateRemaining with
  | done value =>
      exact done_step table value remaining state graphCalls
        signedMessages bad tests spent privateRemaining limit bounded
  | coin n next ih =>
      change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
      exact coin_step table n next remaining state graphCalls
        signedMessages bad tests spent limit
        (fun answer => ih answer remaining state graphCalls
          signedMessages bad tests spent privateRemaining
          (budget answer) bounded)
  | sign index next ih =>
      change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
      exact sign_step table index next remaining state graphCalls
        signedMessages bad tests spent privateRemaining limit budget bounded
        (fun answer updated nextBudget =>
          ih answer remaining updated graphCalls signedMessages
            bad tests spent privateRemaining nextBudget bounded)
  | privateHash input outside next ih =>
      change 0 < privateRemaining ∧ ∀ answer,
        PrivateBudget (privateRemaining - 1) (next answer) at budget
      exact private_step table input outside next remaining state graphCalls
        signedMessages bad tests spent privateRemaining limit budget bounded
        (fun answer updated messages nextBudget nextBound =>
          ih answer remaining updated graphCalls messages bad tests
            (spent + 1) (privateRemaining - 1) nextBudget nextBound)
  | hash input next ih =>
      change ∀ answer, PrivateBudget privateRemaining (next answer) at budget
      exact hash_step table input next remaining state graphCalls
        signedMessages bad tests spent privateRemaining limit budget bounded
        (fun answer updated graphCalls bad tests nextBudget =>
          ih answer (remaining - 1) updated graphCalls signedMessages
            bad tests spent privateRemaining nextBudget bounded)

theorem global_marks_le_double_lifetime {α : Type}
    (view : QueryCache PointSpec → View α) (remaining : Nat)
    (budget : ∀ cache, PrivateBudget (2 * LIFETIME) (view cache)) :
    ∀ result ∈ support
      (SecurityIndexProgram.execute (global view remaining)),
      SecurityIndexTrace.marks result.2 ≤ 2 * LIFETIME := by
  have credit :
      MarkedCredit (fun _ : JointOutcome α => 2 * LIFETIME) 0
        (global view remaining) := by
    unfold global
    apply unmarked_credit
    intro table
    change MarkedCredit (fun _ : JointOutcome α => 2 * LIFETIME) 0
      (compile table
        (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
        (GroupedBalancedGraphMonitorSignBound67.initial
          (GroupedBalancedGraphMonitorSetup67.cache table))
        0 ∅ false 0)
    exact compile_budget table _ remaining _ 0 ∅ false 0
      0 (2 * LIFETIME) (2 * LIFETIME)
      (budget _) (by omega)
  intro result member
  have bound := marked_execute _ 0 _ credit result member
  simpa only [Nat.zero_add] using bound

#print axioms global_marks_le_double_lifetime

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointLifetime67

end

/-! The organizer's adaptive wire adversary fits the exact shared graph/H5
contact budget in one passive run. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointOrganizerBound67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleComp.EvalDist OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexJointGlobal67
open GroupedBalancedGraphIndexJointViewBudget67
set_option backward.isDefEq.respectTransparency false
open scoped Classical

noncomputable def organizerView (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds : Nat) :
    QueryCache PointSpec → GroupedBalancedGraphMonitorSignCompiler67.View
      (GroupedBalancedGraphOrganizerView67.Result sizes) :=
  fun exposed =>
    let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
    GroupedBalancedGraphInteraction67.toView secretKey exposed
      (GroupedBalancedGraphOrganizerView67.ofInteract sizes
        encode decodeWitness decodeSignature adversary pk rounds
        (adversary.initial pk publicCache) {})

theorem organizer_budget (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds : Nat)
    (exposed : QueryCache PointSpec) :
    PrivateBudget (2 * LIFETIME)
      (organizerView sizes encode decodeWitness decodeSignature
        secretKey adversary publicCache rounds exposed) := by
  unfold organizerView
  let pk := GroupedBalancedGraphMonitorSetupBound67.rootFrom exposed
  apply to_view_budget
  simpa only [Nat.sub_zero] using
    GroupedBalancedGraphSignBudget67.interact_budget sizes
      encode decodeWitness decodeSignature adversary pk rounds
      (adversary.initial pk publicCache) ({} : SigGolf.Transcript sizes)

theorem organizer_joint_bad_le_expected_total (sizes : Sizes)
    (encode : GroupedBalancedScheme67.Signature → Bytes sizes.signature)
    (decodeWitness : Bytes sizes.witness → GroupedBalancedScheme67.Signature)
    (decodeSignature : Bytes sizes.signature → GroupedBalancedScheme67.Signature)
    (secretKey : SecretKey) (adversary : SigGolf.Adversary sizes)
    (publicCache : Cache) (rounds remaining : Nat) :
    let view := organizerView sizes encode decodeWitness decodeSignature
      secretKey adversary publicCache rounds
    Pr[fun result => result.1.bad = true ∨
      SecurityIndexTrace.Conflict result.2 |
      SecurityIndexProgram.execute (global view remaining)] ≤
    expectedValue (SecurityIndexProgram.execute (global view remaining))
      (fun result =>
        ((result.1.value.graphCalls : ENNReal) + result.2.length : ENNReal)) /
          (2 : ENNReal) ^ 127 := by
  dsimp only
  let view := organizerView sizes encode decodeWitness decodeSignature
    secretKey adversary publicCache rounds
  have lifetime :=
    GroupedBalancedGraphIndexJointLifetime67.global_marks_le_double_lifetime
      view remaining
      (organizer_budget sizes encode decodeWitness decodeSignature
        secretKey adversary publicCache rounds)
  have eventLe :
      Pr[fun result => result.1.bad = true ∨
        SecurityIndexTrace.Conflict result.2 |
        SecurityIndexProgram.execute (global view remaining)] ≤
      Pr[fun result => result.1.bad = true ∨
        (SecurityIndexTrace.Conflict result.2 ∧
          SecurityIndexTrace.marks result.2 ≤ 2 * LIFETIME) |
        SecurityIndexProgram.execute (global view remaining)] := by
    apply probEvent_mono
    intro result member event
    rcases event with graph | index
    · exact Or.inl graph
    · exact Or.inr ⟨index, lifetime result member⟩
  exact eventLe.trans
    (GroupedBalancedGraphIndexJointBound67.joint_double_bad_le_expected_total
      view remaining)

#print axioms organizer_joint_bad_le_expected_total

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointOrganizerBound67
