import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNoncePublic67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPrivate67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCost67. -/
section
/-! A public prereveal nonce guess is recorded only alongside a fresh H5
draw. These elementary accounting facts are used by the stopped compiler. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostStep67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledAudit67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def Affordable (audit : Audit) : Prop :=
  audit.nonceGuesses.length ≤ audit.draws.length

theorem empty : Affordable {} := by simp [Affordable]

theorem signStep (audit : Audit) (pair : Message × Bytes 32)
    (affordable : Affordable audit) :
    Affordable (GroupedBalancedIndexLabeledAudit67.signStep audit pair) := by
  simpa only [Affordable, GroupedBalancedIndexLabeledAudit67.signStep]
    using affordable

theorem drawStep (audit : Audit) (input : Query) (mark : Bool)
    (answer : BitVec 256) (affordable : Affordable audit) :
    Affordable { audit with
      h5cache := audit.h5cache.cacheQuery input answer
      draws := audit.draws ++
        [(input, (mark, answer.extractLsb' 0 160))] } := by
  dsimp only [Affordable] at affordable ⊢
  simp only [List.length_append, List.length_singleton]
  omega

theorem publicDraw (audit : Audit) (pair : Message × Bytes 32)
    (input : Query) (answer : BitVec 256)
    (affordable : Affordable audit) :
    Affordable
      { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
        h5cache :=
          (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery
            input answer
        draws :=
          (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
            [(input, (false, answer.extractLsb' 0 160))] } := by
  by_cases signed : pair.1 ∈ audit.signedMessages
  · simpa only [GroupedBalancedIndexLabeledAudit67.publicStep,
      if_pos signed] using drawStep audit input false answer affordable
  · dsimp only [Affordable] at affordable ⊢
    simp only [GroupedBalancedIndexLabeledAudit67.publicStep,
      if_neg signed, List.length_cons, List.length_append,
      List.length_singleton] at *
    omega

#print axioms publicDraw

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostStep67


namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPrivate67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCostStep67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

theorem some_step {α : Type}
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (signedMessages : Finset Message) (audit : Audit)
    (affordable : Affordable audit)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      Affordable audit' →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        Affordable result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        (some pair) state input signedMessages next) audit),
      Affordable result.2 := by
  intro result member
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run] at member
      exact child answer state (insert pair.1 signedMessages)
        (GroupedBalancedIndexLabeledAudit67.signStep audit pair)
        (signStep audit pair affordable) result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        (insert pair.1 signedMessages)
        (GroupedBalancedIndexLabeledAudit67.signStep
          { audit with
            h5cache := audit.h5cache.cacheQuery input answer
            draws := audit.draws ++
              [(input, (decide (pair.1 ∉ signedMessages),
                answer.extractLsb' 0 160))] } pair)
        (signStep _ pair (drawStep audit input
          (decide (pair.1 ∉ signedMessages)) answer affordable))
        childResult childMember

theorem none_step {α : Type}
    (state : State) (input : Query)
    (signedMessages : Finset Message) (audit : Audit)
    (affordable : Affordable audit)
    (next : BitVec 256 → State → Finset Message →
      Program (JointOutcome α))
    (child : ∀ answer updated signed audit',
      Affordable audit' →
      ∀ result ∈ support (run (next answer updated signed) audit'),
        Affordable result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.privateHashStepOn
        none state input signedMessages next) audit),
      Affordable result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.privateHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_unmarked,
    mem_support_bind_iff] at member
  obtain ⟨sample, _, childMember⟩ := member
  rcases sample with ⟨answer, residual⟩
  exact child answer { state with residual := residual }
    signedMessages audit affordable result childMember

#print axioms some_step
#print axioms none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPrivate67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPublic67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCost67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPublic67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCostStep67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.constructorNameAsVariable false

theorem some_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (pair : Message × Bytes 32)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (affordable : Affordable audit)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      Affordable audit' →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'),
        Affordable result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        (some pair) table state input graphCalls bad tests next) audit),
      Affordable result.2 := by
  intro result member
  cases cached : state.residual input with
  | some answer =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        reduceCtorEq, if_false, run] at member
      exact child answer state graphCalls bad tests audit affordable
        result member
  | none =>
      simp only [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
        GroupedBalancedIndexLabeledLift67.cachedDraw, cached,
        if_true, run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨childResult, childMember, same⟩ := member
      subst result
      exact child answer
        { state with residual := state.residual.cacheQuery input answer }
        graphCalls bad tests
        { GroupedBalancedIndexLabeledAudit67.publicStep audit pair with
          h5cache :=
            (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).h5cache.cacheQuery
              input answer
          draws :=
            (GroupedBalancedIndexLabeledAudit67.publicStep audit pair).draws ++
              [(input, (false, answer.extractLsb' 0 160))] }
        (publicDraw audit pair input answer affordable)
        childResult childMember

theorem none_step {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (audit : Audit) (affordable : Affordable audit)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program (JointOutcome α))
    (child : ∀ answer updated calls bad tests audit',
      Affordable audit' →
      ∀ result ∈ support (run
        (next answer updated calls bad tests) audit'),
        Affordable result.2) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.publicHashStepOn
        none table state input graphCalls bad tests next) audit),
      Affordable result.2 := by
  intro result member
  rw [GroupedBalancedIndexLabeledJoint67.publicHashStepOn,
    GroupedBalancedIndexLabeledAuditLift67.run_ofGraphKeep,
    mem_support_bind_iff] at member
  obtain ⟨graphResult, _, childMember⟩ := member
  exact child graphResult.value.1
    (opened state graphResult.value.2.1 graphResult.value.2.2)
    (graphCalls + if (GroupedBalancedGraphQuery67.locate input).isSome
      then 1 else 0)
    (bad || graphResult.bad) (tests + graphResult.tests)
    audit affordable result childMember

#print axioms some_step
#print axioms none_step

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCostPublic67

end

/-! Each prereveal public H5 pair in the stopped audit has a distinct
fresh H5 draw to pay for it. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCost67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledNonceCostStep67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
open scoped Classical

theorem compile_affordable {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) (audit : Audit)
    (affordable : Affordable audit) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.compile table view remaining
        state graphCalls signedMessages bad tests) audit),
      Affordable result.2 := by
  induction view generalizing remaining state graphCalls signedMessages bad tests audit with
  | done value =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact affordable
  | coin n next ih =>
      intro result member
      simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
        mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer remaining state graphCalls signedMessages bad tests
        audit affordable result child
  | sign index next ih =>
      intro result member
      change result ∈ support (run
        (GroupedBalancedIndexLabeledJoint67.compile table
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls
          signedMessages bad tests) audit) at member
      exact ih (table (.inr (.inl index))) remaining
        (signed state index (table (.inr (.inl index)))) graphCalls
        signedMessages bad tests audit affordable result member
  | privateHash input outside next ih =>
      intro result member
      cases parsed : SecurityIndexQuery.parse input with
      | some pair =>
          exact GroupedBalancedIndexLabeledNonceCostPrivate67.some_step
            state input pair signedMessages audit affordable
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' affordable' =>
              ih answer remaining updated graphCalls signed bad tests
                audit' affordable')
            result (by
              unfold GroupedBalancedIndexLabeledJoint67.compile at member
              rw [parsed] at member
              exact member)
      | none =>
          exact GroupedBalancedIndexLabeledNonceCostPrivate67.none_step
            state input signedMessages audit affordable
            (fun answer updated signed =>
              GroupedBalancedIndexLabeledJoint67.compile table
                (next answer) remaining updated graphCalls signed bad tests)
            (fun answer updated signed audit' affordable' =>
              ih answer remaining updated graphCalls signed bad tests
                audit' affordable')
            result (by
              unfold GroupedBalancedIndexLabeledJoint67.compile at member
              rw [parsed] at member
              exact member)
  | hash input next ih =>
      intro result member
      cases remaining with
      | zero =>
          simp only [GroupedBalancedIndexLabeledJoint67.compile, run,
            support_pure, Set.mem_singleton_iff] at member
          subst result
          exact affordable
      | succ remaining =>
          cases parsed : SecurityIndexQuery.parse input with
          | some pair =>
              exact GroupedBalancedIndexLabeledNonceCostPublic67.some_step
                table state input pair graphCalls bad tests audit affordable
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' affordable' =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' affordable')
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)
          | none =>
              exact GroupedBalancedIndexLabeledNonceCostPublic67.none_step
                table state input graphCalls bad tests audit affordable
                (fun answer updated calls bad tests =>
                  GroupedBalancedIndexLabeledJoint67.compile table
                    (next answer) remaining updated calls signedMessages
                    bad tests)
                (fun answer updated calls bad tests audit' affordable' =>
                  ih answer remaining updated calls signedMessages bad tests
                    audit' affordable')
                result (by
                  unfold GroupedBalancedIndexLabeledJoint67.compile at member
                  rw [parsed] at member
                  exact member)

theorem start_affordable {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    ∀ result ∈ support (run
      (GroupedBalancedIndexLabeledJoint67.start table view remaining) {}),
      result.2.nonceGuesses.length ≤ result.1.2.length := by
  intro result member
  have afford := compile_affordable table
    (view (GroupedBalancedGraphMonitorSetup67.cache table)) remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0 {} empty result member
  have draws := GroupedBalancedIndexLabeledCoverage67.run_draws_append
    _ {} result member
  dsimp only [Affordable] at afford
  rw [draws] at afford
  simpa using afford

#print axioms compile_affordable
#print axioms start_affordable

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledNonceCost67
