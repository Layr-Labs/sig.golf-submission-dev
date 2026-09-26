import SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobal67
import SigGolfCandidate.Hypertree.GroupedBalancedNonceSafeProgram67

/-! The concrete stopped interaction has no public query between a nonce
read and its corresponding sign record. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobalSafe67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedNonceProgram67
open GroupedBalancedNonceSafeProgram67
open GroupedBalancedNonceView67
open GroupedBalancedNonceJointCompiler67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphPassive67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped Classical

mutual
  theorem safe_bind {α β : Type} (program : Program α)
      (next : α → Program β) (safe : Safe program)
      (children : ∀ value, Safe (next value)) :
      Safe (bind program next) := by
    cases safe with
    | pure value => exact children value
    | draw input mark resume good =>
        exact Safe.draw input mark _ (fun answer =>
          safe_bind (resume answer) next (good answer) children)
    | recordPublic pair resume good =>
        exact Safe.recordPublic pair _
          (safe_bind resume next good children)
    | recordSign pair resume good =>
        exact Safe.recordSign pair _
          (safe_bind resume next good children)
    | coin n resume good =>
        exact Safe.coin n _ (fun answer =>
          safe_bind (resume answer) next (good answer) children)
    | nonce message resume good =>
        exact Safe.nonce message _ (fun answer =>
          pending_bind message (resume answer) next (good answer) children)

  theorem pending_bind {α β : Type} (message : Message)
      (program : Program α) (next : α → Program β)
      (pending : Pending message program)
      (children : ∀ value, Safe (next value)) :
      Pending message (bind program next) := by
    cases pending with
    | recordSign _ pair same resume good =>
        exact Pending.recordSign message pair same _
          (safe_bind resume next good children)
    | draw _ input mark resume good =>
        exact Pending.draw message input mark _ (fun answer =>
          pending_bind message (resume answer) next
            (good answer) children)
end

theorem safe_fromLabeled {α : Type}
    (program : GroupedBalancedIndexLabeledProgram67.Program α) :
    Safe (fromLabeled program) := by
  induction program with
  | pure value => exact Safe.pure value
  | draw input mark resume ih =>
      exact Safe.draw input mark _ ih
  | recordPublic pair resume ih =>
      exact Safe.recordPublic pair _ ih
  | recordSign pair resume ih =>
      exact Safe.recordSign pair _ ih
  | coin n resume ih =>
      exact Safe.coin n _ ih

theorem safe_unmarked {α β : Type} (program : ProbComp α)
    (next : α → Program β) (children : ∀ value, Safe (next value)) :
    Safe (GroupedBalancedNonceGlobal67.unmarked program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact children value
  | query_bind n resume ih =>
      exact Safe.coin n _ (fun answer => ih answer)

theorem safe_privateStep (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (input : Query) (signedMessages : Finset Message) :
    Safe (privateStep state input signedMessages) := by
  unfold privateStep
  exact safe_fromLabeled _

theorem safe_publicStep (table : GroupedBalancedGraphPassive67.PointTable)
    (state : GroupedBalancedGraphMonitorSignCompiler67.State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat) :
    Safe (publicStep table state input graphCalls bad tests) := by
  unfold publicStep
  exact safe_fromLabeled _

mutual
  inductive Good {α : Type} : NView α → Prop where
    | done (value : α) : Good (.done value)
    | hash (input : Query) (next : BitVec 256 → NView α)
        (children : ∀ answer, Good (next answer)) :
        Good (.hash input next)
    | privateHash (input : Query)
        (outside : GroupedBalancedGraphQuery67.locate input = none)
        (next : BitVec 256 → NView α)
        (children : ∀ answer, Good (next answer)) :
        Good (.privateHash input outside next)
    | sign (index : BitVec 160) (next : BitVec 256 → NView α)
        (children : ∀ answer, Good (next answer)) :
        Good (.sign index next)
    | coin (n : Nat) (next : Fin (n+1) → NView α)
        (children : ∀ answer, Good (next answer)) :
        Good (.coin n next)
    | nonce (message : Message) (next : BitVec 256 → NView α)
        (children : ∀ answer, Await message (next answer)) :
        Good (.nonce message next)

  inductive Await {α : Type} : Message → NView α → Prop where
    | privateHash (message : Message) (randomizer : Bytes 32)
        (outside : GroupedBalancedGraphQuery67.locate
          (SecurityRandomOracle.indexInput message randomizer) = none)
        (next : BitVec 256 → NView α)
        (children : ∀ answer, Good (next answer)) :
        Await message (.privateHash
          (SecurityRandomOracle.indexInput message randomizer)
          outside next)
end

mutual
  theorem good_map {α β : Type} (f : α → β) (view : NView α)
      (good : Good view) :
      Good (GroupedBalancedNonceView67.map f view) := by
    cases good with
    | done value => exact Good.done _
    | hash input next children =>
        exact Good.hash input _ (fun answer =>
          good_map f (next answer) (children answer))
    | privateHash input outside next children =>
        exact Good.privateHash input outside _ (fun answer =>
          good_map f (next answer) (children answer))
    | sign index next children =>
        exact Good.sign index _ (fun answer =>
          good_map f (next answer) (children answer))
    | coin n next children =>
        exact Good.coin n _ (fun answer =>
          good_map f (next answer) (children answer))
    | nonce message next children =>
        exact Good.nonce message _ (fun answer =>
          await_map f message (next answer) (children answer))

  theorem await_map {α β : Type} (f : α → β) (message : Message)
      (view : NView α) (await : Await message view) :
      Await message (GroupedBalancedNonceView67.map f view) := by
    cases await with
    | privateHash _ randomizer outside next children =>
        exact Await.privateHash message randomizer outside _
          (fun answer => good_map f (next answer) (children answer))
end

theorem good_prependAction {α : Type}
    (action : GroupedBalancedGameQueryTrace67.Action)
    (view : NView (α × List GroupedBalancedGameQueryTrace67.Action))
    (good : Good view) : Good (prependAction action view) := by
  exact good_map _ view good

mutual
  theorem good_annotate {α : Type} (view : NView α)
      (secret : Nat) (good : Good view) :
      Good (GroupedBalancedNonceClassView67.annotate view secret) := by
    cases good with
    | done value => exact Good.done _
    | hash input next children =>
        exact Good.hash input _ (fun answer =>
          good_annotate (next answer)
            (secret + GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)
            (children answer))
    | privateHash input outside next children =>
        exact Good.privateHash input outside _ (fun answer =>
          good_annotate (next answer) secret (children answer))
    | sign index next children =>
        exact Good.sign index _ (fun answer =>
          good_annotate (next answer) secret (children answer))
    | coin n next children =>
        exact Good.coin n _ (fun answer =>
          good_annotate (next answer) secret (children answer))
    | nonce message next children =>
        exact Good.nonce message _ (fun answer =>
          await_annotate message (next answer) secret (children answer))

  theorem await_annotate {α : Type} (message : Message)
      (view : NView α) (secret : Nat) (await : Await message view) :
      Await message
        (GroupedBalancedNonceClassView67.annotate view secret) := by
    cases await with
    | privateHash _ randomizer outside next children =>
        exact Await.privateHash message randomizer outside _
          (fun answer => good_annotate (next answer) secret
            (children answer))
end

theorem good_cutoff {α : Type}
    (cache : QueryCache PointSpec) (interaction : Interaction α)
    (budget : Nat) :
    Good (GroupedBalancedNonceView67.cutoff cache interaction budget) := by
  induction interaction generalizing budget with
  | done value => exact Good.done _
  | coin n next ih =>
      exact Good.coin n _ (fun answer => ih answer budget)
  | hash input next ih =>
      cases budget with
      | zero => exact Good.done _
      | succ remaining =>
          exact Good.hash input _ (fun answer =>
            good_prependAction _ _ (ih answer remaining))
  | sign message next ih =>
      cases budget with
      | zero => exact Good.done _
      | succ remaining =>
          cases remaining with
          | zero =>
              exact good_prependAction _ _ (Good.done _)
          | succ remaining =>
              apply good_prependAction
              apply Good.nonce message
              intro randomizer
              apply Await.privateHash message randomizer
                (GroupedBalancedGraphHonestSignView67.locate_index_none
                  message randomizer)
              intro indexAnswer
              apply Good.sign
              intro bottomAnswer
              exact good_prependAction _ _
                (ih (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
                  cache randomizer (indexAnswer.extractLsb' 0 160)
                  bottomAnswer) remaining)

theorem pending_index_step {β : Type}
    (message : Message) (randomizer : Bytes 32)
    (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (signedMessages : Finset Message)
    (next : BitVec 256 → GroupedBalancedGraphMonitorSignCompiler67.State →
      Finset Message → Program β)
    (children : ∀ answer updated signed, Safe (next answer updated signed)) :
    Pending message
      (bind (privateStep state
        (SecurityRandomOracle.indexInput message randomizer)
        signedMessages)
        (fun ⟨answer, updated, signed⟩ => next answer updated signed)) := by
  unfold privateStep
  rw [SecurityIndexQuery.parse_index]
  unfold GroupedBalancedIndexLabeledJoint67.privateHashStepOn
  unfold GroupedBalancedIndexLabeledLift67.cachedDraw
  cases present : state.residual
      (SecurityRandomOracle.indexInput message randomizer) with
  | some answer =>
      simp only [present, fromLabeled, GroupedBalancedNonceProgram67.bind]
      exact Pending.recordSign message (message, randomizer) rfl _
        (children answer state (insert message signedMessages))
  | none =>
      simp only [present, fromLabeled, GroupedBalancedNonceProgram67.bind]
      apply Pending.draw message
      intro answer
      exact Pending.recordSign message (message, randomizer) rfl _
        (children answer
          { state with residual :=
            (state.residual.cacheQuery
              (SecurityRandomOracle.indexInput message randomizer) answer) }
          (insert message signedMessages))

mutual
  theorem safe_compile {α : Type}
      (table : PointTable) (view : NView α)
      (remaining : Nat)
      (state : GroupedBalancedGraphMonitorSignCompiler67.State)
      (graphCalls : Nat) (signedMessages : Finset Message)
      (bad : Bool) (tests : Nat) (good : Good view) :
      Safe (compile table view remaining state graphCalls
        signedMessages bad tests) := by
    cases good with
    | done value => exact Safe.pure _
    | coin n next children =>
        exact Safe.coin n _ (fun answer =>
          safe_compile table (next answer) remaining state graphCalls
            signedMessages bad tests (children answer))
    | sign index next children =>
        exact safe_compile table (next (table (.inr (.inl index))))
          remaining
          (GroupedBalancedGraphMonitorSignCompiler67.signed state index
            (table (.inr (.inl index))))
          graphCalls signedMessages bad tests
          (children (table (.inr (.inl index))))
    | privateHash input outside next children =>
        apply safe_bind
        · exact safe_privateStep state input signedMessages
        · intro value
          rcases value with ⟨answer, updated, signed⟩
          exact safe_compile table (next answer) remaining updated graphCalls
            signed bad tests (children answer)
    | hash input next children =>
        cases remaining with
        | zero => exact Safe.pure _
        | succ remaining =>
            apply safe_bind
            · exact safe_publicStep table state input graphCalls bad tests
            · intro value
              rcases value with ⟨answer, updated, calls, bad', tests'⟩
              exact safe_compile table (next answer) remaining updated calls
                signedMessages bad' tests' (children answer)
    | nonce message next children =>
        exact Safe.nonce message _ (fun answer =>
          pending_compile message table (next answer) remaining state
            graphCalls signedMessages bad tests (children answer))

  theorem pending_compile {α : Type} (message : Message)
      (table : PointTable) (view : NView α)
      (remaining : Nat)
      (state : GroupedBalancedGraphMonitorSignCompiler67.State)
      (graphCalls : Nat) (signedMessages : Finset Message)
      (bad : Bool) (tests : Nat) (await : Await message view) :
      Pending message (compile table view remaining state graphCalls
        signedMessages bad tests) := by
    cases await with
    | privateHash _ randomizer outside next children =>
        exact pending_index_step message randomizer state signedMessages
          (fun answer updated signed =>
            compile table (next answer) remaining updated graphCalls
              signed bad tests)
          (fun answer updated signed =>
            safe_compile table (next answer) remaining updated graphCalls
              signed bad tests (children answer))
end

theorem safe_global {α : Type}
    (interaction : QueryCache PointSpec → Interaction α)
    (budget : Nat) :
    Safe (GroupedBalancedNonceGlobal67.global interaction budget) := by
  unfold GroupedBalancedNonceGlobal67.global
  apply safe_unmarked
  intro table
  unfold GroupedBalancedNonceJointCompiler67.start
  apply safe_compile
  exact good_annotate _ 0 (good_cutoff _ _ budget)

#print axioms safe_bind
#print axioms pending_bind
#print axioms safe_fromLabeled
#print axioms safe_unmarked
#print axioms good_cutoff
#print axioms pending_index_step
#print axioms safe_compile
#print axioms safe_global
end SigGolfCandidate.Hypertree.GroupedBalancedNonceGlobalSafe67
