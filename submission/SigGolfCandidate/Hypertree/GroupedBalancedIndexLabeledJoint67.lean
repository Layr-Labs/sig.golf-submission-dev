import SigGolfCandidate.Hypertree.SecurityIndexProgram
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJoint67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledLift67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67. -/
section
/-! A ghost input label on each fresh H5 draw. Erasing the label preserves
the exact outcome and unlabelled trace distribution. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledProgram67
open SigGolf OracleComp OracleSpec Reference
open SecurityIndexTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev Draw := Query × Entry

inductive Program (α : Type) where
  | pure (value : α)
  | draw (input : Query) (mark : Bool)
      (next : BitVec 256 → Program α)
  | recordPublic (pair : Message × Bytes 32) (next : Program α)
  | recordSign (pair : Message × Bytes 32) (next : Program α)
  | coin (n : Nat) (next : Fin (n + 1) → Program α)

def erase {α : Type} : Program α → SecurityIndexProgram.Program α
  | .pure value => .pure value
  | .draw _ mark next => .draw mark (fun answer => erase (next answer))
  | .recordPublic _ next => erase next
  | .recordSign _ next => erase next
  | .coin n next => .coin n (fun answer => erase (next answer))

noncomputable def execute {α : Type} :
    Program α → ProbComp (α × List Draw)
  | .pure value => pure (value, [])
  | .draw input mark next => do
      let answer ← $ᵗ BitVec 256
      (fun result =>
        (result.1, (input, (mark, answer.extractLsb' 0 160)) :: result.2))
        <$> execute (next answer)
  | .recordPublic _ next => execute next
  | .recordSign _ next => execute next
  | .coin n next => do
      let answer ← $ᵗ Fin (n + 1)
      execute (next answer)

theorem execute_erasure {α : Type} (program : Program α) :
    (fun result => (result.1, result.2.map Prod.snd)) <$>
      execute program = SecurityIndexProgram.execute (erase program) := by
  induction program with
  | pure value => rfl
  | recordPublic pair next ih => exact ih
  | recordSign message next ih => exact ih
  | coin n next ih =>
      simp only [execute, erase, SecurityIndexProgram.execute, map_bind]
      exact bind_congr ih
  | draw input mark next ih =>
      simp only [execute, erase, SecurityIndexProgram.execute, map_bind,
        Functor.map_map]
      apply bind_congr
      intro answer
      rw [← ih answer]
      simp only [Functor.map_map, Function.comp_def, List.map_cons]

#print axioms execute_erasure

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledProgram67


/-! Input-labelled copies of the residual-cache and graph lifts used by the
joint monitor, with exact erasure to its original program. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledLift67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedIndexLabeledProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

noncomputable def cachedDraw {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec → Program α) : Program α :=
  match residual input with
  | some answer => next answer residual
  | none => .draw input mark (fun answer =>
      next answer (residual.cacheQuery input answer))

theorem erase_cachedDraw {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec → Program α) :
    erase (cachedDraw residual input mark next) =
      GroupedBalancedGraphIndexJoint67.cachedDraw residual input mark
        (fun answer cache => erase (next answer cache)) := by
  cases present : residual input <;>
    simp only [cachedDraw, GroupedBalancedGraphIndexJoint67.cachedDraw,
      present, erase]

def unmarked {α β : Type} (program : ProbComp α)
    (next : α → Program β) : Program β :=
  OracleComp.construct next (fun n _ continuation => .coin n continuation)
    program

theorem erase_unmarked {α β : Type} (program : ProbComp α)
    (next : α → Program β) :
    erase (unmarked program next) =
      GroupedBalancedGraphIndexLift67.unmarked program
        (fun result => erase (next result)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind n resume ih =>
      change erase (.coin n (fun answer =>
        unmarked (resume answer) next)) =
        SecurityIndexProgram.Program.coin n (fun answer =>
          GroupedBalancedGraphIndexLift67.unmarked
            (resume answer) (fun value => erase (next value)))
      simp only [erase, ih]

noncomputable def ofGraphKeep {α β : Type} (table : PointTable) :
    QueryCache PointSpec →
    GroupedBalancedGraphMonitorProgram67.Program α →
    (GroupedBalancedGraphMonitorProgram67.Outcome α → Program β) →
    Program β
  | _, .done value, next => next ⟨value, false, 0⟩
  | cache, .reveal point resume, next =>
      ofGraphKeep table (cache.cacheQuery point (table point))
        (resume (table point)) next
  | cache, .guess point value resume, next =>
      ofGraphKeep table cache resume (fun result =>
        next (GroupedBalancedGraphMonitorProgram67.addTest
          (decide (cache point = none ∧ truncate (table point) = value))
          result))
  | cache, .coin n resume, next =>
      .coin n (fun answer => ofGraphKeep table cache (resume answer) next)
  | cache, .bits resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraphKeep table cache (resume answer) next)
  | cache, .collision target resume, next =>
      unmarked ($ᵗ BitVec 256)
        (fun answer => ofGraphKeep table cache (resume answer)
          (fun result => next
            (GroupedBalancedGraphMonitorProgram67.addTest
              (decide (truncate answer = target)) result)))

theorem erase_ofGraphKeep {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program α)
    (next : GroupedBalancedGraphMonitorProgram67.Outcome α → Program β) :
    erase (ofGraphKeep table cache program next) =
      GroupedBalancedGraphIndexKeep67.ofGraphKeep table cache program
        (fun result => erase (next result)) := by
  induction program generalizing cache next with
  | done value => rfl
  | reveal point resume ih => exact ih (table point) _ _
  | guess point value resume ih => exact ih cache _
  | coin n resume ih =>
      simp only [ofGraphKeep, erase,
        GroupedBalancedGraphIndexKeep67.ofGraphKeep]
      exact congrArg _ (funext fun answer => ih answer cache next)
  | bits resume ih =>
      rw [ofGraphKeep, erase_unmarked]
      change _ = GroupedBalancedGraphIndexKeep67.ofGraphKeep table cache
        (.bits resume) (fun result => erase (next result))
      simp only [GroupedBalancedGraphIndexKeep67.ofGraphKeep]
      exact congrArg _ (funext fun answer => ih answer cache next)
  | collision target resume ih =>
      rw [ofGraphKeep, erase_unmarked]
      change _ = GroupedBalancedGraphIndexKeep67.ofGraphKeep table cache
        (.collision target resume) (fun result => erase (next result))
      simp only [GroupedBalancedGraphIndexKeep67.ofGraphKeep]
      exact congrArg _ (funext fun answer => ih answer cache _)

#print axioms erase_cachedDraw
#print axioms erase_unmarked
#print axioms erase_ofGraphKeep

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledLift67
end

/-! The direct67 joint compiler with ghost H5 input labels. Its erasure is
definitionally the same graph/H5 execution at every interaction step. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledProgram67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped Classical

noncomputable def privateHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query)
    (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message →
      Program α) : Program α :=
  match parsed with
  | some pair =>
      GroupedBalancedIndexLabeledLift67.cachedDraw
        state.residual input (decide (pair.1 ∉ signedMessages))
        (fun answer residual =>
          .recordSign pair
            (next answer { state with residual := residual }
              (insert pair.1 signedMessages)))
  | none =>
      GroupedBalancedIndexLabeledLift67.unmarked
        ((randomOracle (spec := HashSpec) input).run state.residual)
        (fun result =>
          next result.1 { state with residual := result.2 } signedMessages)

noncomputable def publicHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (table : PointTable) (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat →
      Program α) : Program α :=
  match parsed with
  | some pair =>
      let continuation :=
        GroupedBalancedIndexLabeledLift67.cachedDraw
          state.residual input false (fun answer residual =>
            next answer { state with residual := residual }
              graphCalls bad tests)
      if state.residual input = none then
        .recordPublic pair continuation
      else continuation
  | none =>
      GroupedBalancedIndexLabeledLift67.ofGraphKeep
        table state.exposed
        (GroupedBalancedGraphMonitorOracle67.publicStep
          state.exposed state.residual input
          (fun answer exposed residual =>
            .done (answer, exposed, residual)))
        (fun result =>
          let graphCalls' := graphCalls +
            if (GroupedBalancedGraphQuery67.locate input).isSome
            then 1 else 0
          next result.value.1
            (opened state result.value.2.1 result.value.2.2)
            graphCalls' (bad || result.bad) (tests + result.tests))

noncomputable def compile {α : Type} (table : PointTable) :
    View α → Nat → State → Nat → Finset Message → Bool → Nat →
    Program (JointOutcome α)
  | .done value, remaining, state, graphCalls, _, bad, tests =>
      .pure ⟨⟨some value, remaining, state, graphCalls⟩, bad, tests⟩
  | .coin n next, remaining, state, graphCalls, signedMessages, bad, tests =>
      .coin n (fun answer => compile table (next answer) remaining state
        graphCalls signedMessages bad tests)
  | .sign index next, remaining, state, graphCalls, signedMessages, bad, tests =>
      let answer := table (.inr (.inl index))
      compile table (next answer) remaining (signed state index answer)
        graphCalls signedMessages bad tests
  | .privateHash input _ next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      privateHashStepOn (SecurityIndexQuery.parse input) state input
        signedMessages (fun answer updated signedMessages =>
          compile table (next answer) remaining updated graphCalls
            signedMessages bad tests)
  | .hash input next, remaining, state, graphCalls,
      signedMessages, bad, tests =>
      match remaining with
      | 0 => .pure ⟨⟨none, 0, state, graphCalls⟩, bad, tests⟩
      | remaining + 1 =>
          publicHashStepOn (SecurityIndexQuery.parse input) table state input
            graphCalls bad tests
            (fun answer updated graphCalls bad tests =>
              compile table (next answer) remaining updated graphCalls
                signedMessages bad tests)

noncomputable def start {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    Program (JointOutcome α) :=
  compile table (view (GroupedBalancedGraphMonitorSetup67.cache table))
    remaining
    (GroupedBalancedGraphMonitorSignBound67.initial
      (GroupedBalancedGraphMonitorSetup67.cache table))
    0 ∅ false 0

theorem erase_privateHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (state : State) (input : Query)
    (signedMessages : Finset Message)
    (next : BitVec 256 → State → Finset Message → Program α) :
    erase (privateHashStepOn parsed state input signedMessages next) =
      GroupedBalancedGraphIndexJoint67.privateHashStepOn
        parsed state input signedMessages
        (fun answer state signedMessages =>
          erase (next answer state signedMessages)) := by
  cases parsed with
  | none =>
      simp only [privateHashStepOn,
        GroupedBalancedGraphIndexJoint67.privateHashStepOn]
      exact GroupedBalancedIndexLabeledLift67.erase_unmarked _ _
  | some pair =>
      simp only [privateHashStepOn,
        GroupedBalancedGraphIndexJoint67.privateHashStepOn]
      exact GroupedBalancedIndexLabeledLift67.erase_cachedDraw _ _ _ _

theorem erase_publicHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32))
    (table : PointTable) (state : State) (input : Query)
    (graphCalls : Nat) (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat → Program α) :
    erase (publicHashStepOn parsed table state input graphCalls bad tests next) =
      GroupedBalancedGraphIndexJoint67.publicHashStepOn
        parsed table state input graphCalls bad tests
        (fun answer state calls bad tests =>
          erase (next answer state calls bad tests)) := by
  cases parsed with
  | none =>
      simp only [publicHashStepOn,
        GroupedBalancedGraphIndexJoint67.publicHashStepOn]
      exact GroupedBalancedIndexLabeledLift67.erase_ofGraphKeep _ _ _ _
  | some pair =>
      simp only [publicHashStepOn,
        GroupedBalancedGraphIndexJoint67.publicHashStepOn]
      split <;>
        simpa only [erase] using
          (GroupedBalancedIndexLabeledLift67.erase_cachedDraw
            state.residual input false
            (fun answer residual =>
              next answer { state with residual := residual }
                graphCalls bad tests))

theorem erase_compile {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    erase (compile table view remaining state graphCalls signedMessages bad tests) =
      GroupedBalancedGraphIndexJoint67.compile table view remaining state
        graphCalls signedMessages bad tests := by
  induction view generalizing remaining state graphCalls signedMessages bad tests with
  | done value => rfl
  | coin n next ih =>
      simp only [compile, erase,
        GroupedBalancedGraphIndexJoint67.compile]
      exact congrArg _ (funext fun answer => ih answer _ _ _ _ _ _)
  | sign index next ih =>
      exact ih (table (.inr (.inl index))) _ _ _ _ _ _
  | privateHash input outside next ih =>
      simp only [compile, GroupedBalancedGraphIndexJoint67.compile,
        erase_privateHashStepOn]
      congr 1
      funext answer updated signedMessages
      exact ih answer _ _ _ _ _ _
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [compile, GroupedBalancedGraphIndexJoint67.compile,
            erase_publicHashStepOn]
          congr 1
          funext answer updated graphCalls bad tests
          exact ih answer _ _ _ _ _ _

theorem erase_start {α : Type} (table : PointTable)
    (view : QueryCache PointSpec → View α) (remaining : Nat) :
    erase (start table view remaining) =
      GroupedBalancedGraphIndexJoint67.start table view remaining := by
  exact erase_compile table _ _ _ _ _ _ _

#print axioms erase_compile
#print axioms erase_start

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67
