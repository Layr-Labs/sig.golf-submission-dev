import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledPrepend67
import SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledJoint67
import SigGolfCandidate.Hypertree.GroupedBalancedIdealEagerCutoff67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteractionGame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPureLift67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerProgram67. -/
section
/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPure67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPureLift67. -/
section
/-! A predicate of every terminal branch of a labeled Program. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPure67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAudit67
open GroupedBalancedIndexLabeledMapProgram67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def AllPure {α : Type} (P : α → Prop) : Program α → Prop
  | .pure value => P value
  | .draw _ _ next => ∀ answer, AllPure P (next answer)
  | .recordPublic _ next => AllPure P next
  | .recordSign _ next => AllPure P next
  | .coin _ next => ∀ answer, AllPure P (next answer)

theorem run_allPure {α : Type} (P : α → Prop) (program : Program α)
    (audit : Audit) (result : (α × List Draw) × Audit)
    (all : AllPure P program)
    (member : result ∈ support (run program audit)) : P result.1.1 := by
  induction program generalizing audit result with
  | pure value =>
      simp only [run, support_pure, Set.mem_singleton_iff] at member
      subst result
      exact all
  | recordPublic pair next ih =>
      exact ih (publicStep audit pair) result all member
  | recordSign pair next ih =>
      exact ih (signStep audit pair) result all member
  | coin n next ih =>
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, child⟩ := member
      exact ih answer audit result (all answer) child
  | draw input mark next ih =>
      simp only [run, mem_support_bind_iff] at member
      obtain ⟨answer, _, member⟩ := member
      simp only [support_map, Set.mem_image] at member
      obtain ⟨child, childMember, same⟩ := member
      have childProp := ih answer
        { audit with
          h5cache := audit.h5cache.cacheQuery input answer
          draws := audit.draws ++
            [(input, (mark, answer.extractLsb' 0 160))] }
        child (all answer) childMember
      have eq := congrArg (fun x : (α × List Draw) × Audit => x.1.1) same
      rw [← eq]
      exact childProp

theorem mapProgram_allPure {α β : Type} (P : β → Prop)
    (f : α → β) (program : Program α)
    (all : AllPure (fun value => P (f value)) program) :
    AllPure P (mapProgram f program) := by
  induction program with
  | pure value => exact all
  | recordPublic pair next ih => exact ih all
  | recordSign pair next ih => exact ih all
  | draw input mark next ih => exact fun answer => ih answer (all answer)
  | coin n next ih => exact fun answer => ih answer (all answer)

theorem allPure_mono {α : Type} (P Q : α → Prop)
    (program : Program α) (imp : ∀ value, P value → Q value)
    (all : AllPure P program) : AllPure Q program := by
  induction program with
  | pure value => exact imp value all
  | recordPublic pair next ih => exact ih all
  | recordSign pair next ih => exact ih all
  | draw input mark next ih => exact fun answer => ih answer (all answer)
  | coin n next ih => exact fun answer => ih answer (all answer)

#print axioms run_allPure
#print axioms mapProgram_allPure
#print axioms allPure_mono

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPure67

end

/-! Graph and residual-cache compiler contexts preserve terminal predicates. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPureLift67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledAllPure67
open GroupedBalancedIndexLabeledJoint67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem unmarked_allPure {α β : Type} (P : β → Prop)
    (program : ProbComp α) (next : α → Program β)
    (all : ∀ value, AllPure P (next value)) :
    AllPure P (GroupedBalancedIndexLabeledLift67.unmarked program next) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact all value
  | query_bind n resume ih => exact fun answer => ih answer

theorem cachedDraw_allPure {α : Type} (P : α → Prop)
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec → Program α)
    (all : ∀ answer cache, AllPure P (next answer cache)) :
    AllPure P
      (GroupedBalancedIndexLabeledLift67.cachedDraw
        residual input mark next) := by
  cases cached : residual input with
  | some answer =>
      simpa only [GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached] using all answer residual
  | none =>
      simpa only [GroupedBalancedIndexLabeledLift67.cachedDraw,
        cached, AllPure] using
        (fun answer => all answer (residual.cacheQuery input answer))

theorem ofGraphKeep_allPure {α β : Type} (P : β → Prop)
    (table : PointTable) (cache : QueryCache PointSpec)
    (program : GroupedBalancedGraphMonitorProgram67.Program α)
    (next : GroupedBalancedGraphMonitorProgram67.Outcome α → Program β)
    (all : ∀ result, AllPure P (next result)) :
    AllPure P
      (GroupedBalancedIndexLabeledLift67.ofGraphKeep
        table cache program next) := by
  induction program generalizing cache next with
  | done value => exact all ⟨value, false, 0⟩
  | reveal point resume ih =>
      exact ih (table point) (cache.cacheQuery point (table point)) next all
  | guess point value resume ih =>
      exact ih cache _ (fun result => all _)
  | coin n resume ih => exact fun answer => ih answer cache next all
  | bits resume ih =>
      exact unmarked_allPure P ($ᵗ BitVec 256) _
        (fun answer => ih answer cache next all)
  | collision target resume ih =>
      exact unmarked_allPure P ($ᵗ BitVec 256) _
        (fun answer => ih answer cache _ (fun result => all _))

theorem publicHashStepOn_allPure {α : Type} (P : α → Prop)
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query) (calls : Nat)
    (bad : Bool) (tests : Nat)
    (next : BitVec 256 → State → Nat → Bool → Nat → Program α)
    (all : ∀ answer state calls bad tests,
      AllPure P (next answer state calls bad tests)) :
    AllPure P
      (publicHashStepOn parsed table state input calls bad tests next) := by
  cases parsed with
  | some pair =>
      simp only [publicHashStepOn]
      split
      · exact cachedDraw_allPure P state.residual input false _
          (fun answer residual => all answer
            { state with residual := residual } calls bad tests)
      · exact cachedDraw_allPure P state.residual input false _
          (fun answer residual => all answer
            { state with residual := residual } calls bad tests)
  | none =>
      exact ofGraphKeep_allPure P table state.exposed _ _
        (fun result => all result.value.1
          (opened state result.value.2.1 result.value.2.2)
          (calls + if (GroupedBalancedGraphQuery67.locate input).isSome
            then 1 else 0)
          (bad || result.bad) (tests + result.tests))

#print axioms publicHashStepOn_allPure

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledAllPureLift67
end

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerTerminal67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerProgram67. -/
section
/-! A terminal checker value retains its verifier Boolean through log prefixes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerTerminal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedIndexLabeledMapView67
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def CheckerTerminal {β : Type} (finish : Bool → β)
    (outcome : JointOutcome ((Option β × List Action) × Nat)) : Prop :=
  ∀ value trace secret,
    outcome.value.value = some ((some value, trace), secret) →
    ∃ accepted, value = finish accepted

theorem pure {β : Type} (finish : Bool → β) (accepted : Bool)
    (remaining calls secret : Nat)
    (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (bad : Bool) (tests : Nat) :
    CheckerTerminal finish
      ⟨⟨some ((some (finish accepted), []), secret), remaining,
        state, calls⟩, bad, tests⟩ := by
  intro value trace secretOut equal
  have parts := Option.some.inj equal
  have same : some (finish accepted) = some value :=
    congrArg (fun x => x.1.1) parts
  exact ⟨accepted, (Option.some.inj same).symm⟩

theorem cutoff {β : Type} (finish : Bool → β) (remaining calls : Nat)
    (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (bad : Bool) (tests : Nat) :
    CheckerTerminal finish
      ⟨⟨none, remaining, state, calls⟩, bad, tests⟩ := by
  intro value trace secret equal
  cases equal

theorem eager_cutoff {β : Type} (finish : Bool → β) (secret remaining calls : Nat)
    (state : GroupedBalancedGraphMonitorSignCompiler67.State)
    (bad : Bool) (tests : Nat) :
    CheckerTerminal finish
      ⟨⟨some ((none, []), secret), remaining,
        state, calls⟩, bad, tests⟩ := by
  intro value trace secretOut equal
  have parts := Option.some.inj equal
  have impossible : (none : Option β) = some value :=
    congrArg (fun x => x.1.1) parts
  cases impossible

theorem prepend {β : Type} (finish : Bool → β) (action : Action)
    (outcome : JointOutcome ((Option β × List Action) × Nat))
    (all : CheckerTerminal finish outcome) :
    CheckerTerminal finish
      (mapOutcome
        (fun output : (Option β × List Action) × Nat =>
          ((output.1.1, action :: output.1.2), output.2)) outcome) := by
  intro value trace secret equal
  cases original : outcome.value.value with
  | none =>
      simp only [mapOutcome, original, Option.map_none] at equal
      cases equal
  | some output =>
      rcases output with ⟨⟨maybeValue, innerTrace⟩, innerSecret⟩
      have mapped :
          some ((maybeValue, action :: innerTrace), innerSecret) =
            some ((some value, trace), secret) := by
        simpa only [mapOutcome, original, Option.map_some] using equal
      have parts := Option.some.inj mapped
      have valueSame : maybeValue = some value :=
        congrArg (fun x => x.1.1) parts
      have secretSame : innerSecret = secret :=
        congrArg Prod.snd parts
      have innerValue : outcome.value.value =
          some ((some value, innerTrace), secret) := by
        simpa only [valueSame, secretSame] using original
      exact all value innerTrace secret innerValue

#print axioms prepend

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerTerminal67

end

/-! Every completed terminal branch of the labeled verifier has its declared
checker result, regardless of public query answers or monitor contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerProgram67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedIdealEagerCutoff67
open GroupedBalancedGraphInteractionGame67
open GroupedBalancedIndexLabeledProgram67
open GroupedBalancedIndexLabeledJoint67
open GroupedBalancedIndexLabeledAllPure67
open GroupedBalancedIndexLabeledAllPureLift67
open GroupedBalancedIndexLabeledCheckerTerminal67
open GroupedBalancedIndexLabeledMapView67
open scoped Classical
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false

theorem query_view {β : Type} (input : Query)
    (resume : BitVec 256 → OracleComp HashSpec Bool)
    (finish : Bool → β) (answers : SecurityGraphIdeal.PrivateTable)
    (cache : QueryCache PointSpec) (budget secret : Nat) :
    GroupedBalancedGraphIndexJointClassTrace67.annotate
      (eagerCutoffView answers cache
        (ofHash (liftM (HashSpec.query input) >>= resume)
          (fun accepted => .done (finish accepted))) (budget + 1)) secret =
      .hash input (fun answer =>
        GroupedBalancedGraphIndexJointClassTrace67.annotate
          (GroupedBalancedGameViewLoggedBridge67.prependAction
            (.publicHash input)
            (eagerCutoffView answers cache
              (ofHash (resume answer)
                (fun accepted => .done (finish accepted))) budget))
          (secret +
            GroupedBalancedGraphIndexJointClassTrace67.secretCharge input)) :=
  rfl

theorem checker_program {β : Type} (program : OracleComp HashSpec Bool)
    (finish : Bool → β) (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (budget secret remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    AllPure (CheckerTerminal finish)
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView answers cache
            (ofHash program (fun accepted => .done (finish accepted)))
            budget) secret)
        remaining state calls signedMessages bad tests) := by
  induction program using OracleComp.inductionOn generalizing budget secret
      remaining state calls signedMessages bad tests with
  | pure accepted =>
      exact GroupedBalancedIndexLabeledCheckerTerminal67.pure
        finish accepted remaining calls secret state bad tests
  | query_bind input resume ih =>
      cases budget with
      | zero =>
          exact GroupedBalancedIndexLabeledCheckerTerminal67.eager_cutoff
            finish secret remaining calls state bad tests
      | succ budget =>
          cases remaining with
          | zero =>
              exact GroupedBalancedIndexLabeledCheckerTerminal67.cutoff
                finish 0 calls state bad tests
          | succ remaining =>
              rw [query_view]
              let predicate := CheckerTerminal finish
              let step : BitVec 256 → State → Nat → Bool → Nat →
                  Program (GroupedBalancedGraphIndexJoint67.JointOutcome
                    ((Option β × List Action) × Nat)) :=
                fun answer updated calls' bad' tests' =>
                  compile table
                    (GroupedBalancedGraphIndexJointClassTrace67.annotate
                      (GroupedBalancedGameViewLoggedBridge67.prependAction
                        (.publicHash input)
                        (eagerCutoffView answers cache
                          (ofHash (resume answer)
                            (fun accepted => .done (finish accepted))) budget))
                      (secret +
                        GroupedBalancedGraphIndexJointClassTrace67.secretCharge
                          input)) remaining updated calls' signedMessages
                    bad' tests'
              have stepAll : ∀ answer updated calls' bad' tests',
                  AllPure predicate
                    (step answer updated calls' bad' tests') := by
                intro answer updated calls' bad' tests'
                change AllPure (CheckerTerminal finish)
                  (compile table
                    (GroupedBalancedGraphIndexJointClassTrace67.annotate
                      (GroupedBalancedGameViewLoggedBridge67.prependAction
                        (.publicHash input)
                        (eagerCutoffView answers cache
                          (ofHash (resume answer)
                            (fun accepted => .done (finish accepted))) budget))
                      (secret +
                        GroupedBalancedGraphIndexJointClassTrace67.secretCharge
                          input)) remaining updated calls' signedMessages
                    bad' tests')
                rw [GroupedBalancedIndexLabeledPrepend67.annotated_prepend]
                rw [← GroupedBalancedIndexLabeledMapView67.compile_mapView]
                apply mapProgram_allPure
                apply allPure_mono
                  (CheckerTerminal finish)
                  (fun outcome => CheckerTerminal finish
                    (mapOutcome
                      (fun output : (Option β × List Action) × Nat =>
                        ((output.1.1, .publicHash input :: output.1.2),
                          output.2)) outcome))
                · intro outcome terminal
                  exact GroupedBalancedIndexLabeledCheckerTerminal67.prepend
                    finish (.publicHash input) outcome terminal
                · exact ih answer budget
                    (secret +
                      GroupedBalancedGraphIndexJointClassTrace67.secretCharge
                        input) remaining updated calls' signedMessages bad' tests'
              change AllPure predicate
                (publicHashStepOn (SecurityIndexQuery.parse input)
                  table state input calls bad tests step)
              cases parsed : SecurityIndexQuery.parse input with
              | some pair =>
                  cases cached : state.residual input with
                  | some answer =>
                      simpa only [publicHashStepOn,
                        GroupedBalancedIndexLabeledLift67.cachedDraw,
                        cached, reduceCtorEq, if_false] using
                        (stepAll answer state calls bad tests)
                  | none =>
                      simpa only [publicHashStepOn,
                        GroupedBalancedIndexLabeledLift67.cachedDraw,
                        cached, if_true, AllPure] using
                        (fun answer => stepAll answer
                          { state with residual :=
                            state.residual.cacheQuery input answer }
                          calls bad tests)
              | none =>
                  exact ofGraphKeep_allPure predicate table state.exposed _ _
                    (fun result => stepAll result.value.1
                      (opened state result.value.2.1 result.value.2.2)
                      (calls +
                        if (GroupedBalancedGraphQuery67.locate input).isSome
                        then 1 else 0)
                      (bad || result.bad) (tests + result.tests))

theorem checker_return {β : Type} (program : OracleComp HashSpec Bool)
    (finish : Bool → β) (answers : SecurityGraphIdeal.PrivateTable)
    (table : PointTable) (cache : QueryCache PointSpec)
    (budget secret remaining : Nat) (state : State)
    (calls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat)
    (audit : GroupedBalancedIndexLabeledAudit67.Audit)
    (result :
      (GroupedBalancedGraphIndexJoint67.JointOutcome
        ((Option β × List Action) × Nat) ×
        List GroupedBalancedIndexLabeledProgram67.Draw) ×
        GroupedBalancedIndexLabeledAudit67.Audit)
    (value : β) (trace : List Action) (secretOut : Nat)
    (member : result ∈ support (GroupedBalancedIndexLabeledAudit67.run
      (compile table
        (GroupedBalancedGraphIndexJointClassTrace67.annotate
          (eagerCutoffView answers cache
            (ofHash program (fun accepted => .done (finish accepted)))
            budget) secret)
        remaining state calls signedMessages bad tests) audit))
    (returned : result.1.1.value.value =
      some ((some value, trace), secretOut)) :
    ∃ accepted, value = finish accepted := by
  have all := checker_program program finish answers table cache
    budget secret remaining state calls signedMessages bad tests
  have terminal := GroupedBalancedIndexLabeledAllPure67.run_allPure
    (CheckerTerminal finish) _ audit result all member
  exact terminal value trace secretOut returned

#print axioms checker_program
#print axioms checker_return

end SigGolfCandidate.Hypertree.GroupedBalancedIndexLabeledCheckerProgram67
