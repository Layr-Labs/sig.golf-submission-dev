import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJoint67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSetup67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexObserve67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphRunBind67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointObserve67. -/
section
/-! The passive monitor's local answer and test record compose with the
continuation at the updated exposure cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphRunBind67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorOracle67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

abbrev Answer := BitVec 256 × QueryCache PointSpec × QueryCache HashSpec

def compose {α β : Type} (first : Outcome α) (second : Outcome β) : Outcome β :=
  ⟨second.value, first.bad || second.bad, first.tests + second.tests⟩

theorem compose_clean {α β : Type} (value : α)
    (program : ProbComp (Outcome β)) :
    compose ⟨value, false, 0⟩ <$> program = program := by
  have identity : (compose ⟨value, false, 0⟩ : Outcome β → Outcome β) = id := by
    funext result
    cases result
    simp [compose]
  rw [identity, id_map]

theorem run_residualStep_bind {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    run table exposed (residualStep exposed residual query target next) =
      (run table exposed (residualStep exposed residual query target
        (fun answer opened cache => .done (answer, opened, cache))) >>=
      fun first => compose first <$> run table first.value.2.1
        (next first.value.1 first.value.2.1 first.value.2.2)) := by
  cases present : residual query with
  | some answer =>
      simp only [residualStep, present, run, pure_bind]
      let first : Outcome Answer := ⟨(answer, exposed, residual), false, 0⟩
      have identity :
          (compose first : Outcome α → Outcome α) = id := by
        funext result
        cases result
        simp [first, compose]
      rw [identity, id_map]
  | none =>
      cases known : exposed target with
      | some value =>
          simp only [residualStep, present, known, run, bind_assoc,
            map_eq_pure_bind, pure_bind, compose, addTest]
          apply bind_congr
          intro answer
          apply bind_congr
          intro result
          simp [Bool.or_false, Nat.add_comm]
      | none =>
          simp only [residualStep, present, known, run, bind_assoc,
            map_eq_pure_bind, pure_bind, compose, addTest]
          apply bind_congr
          intro answer
          apply bind_congr
          intro result
          simp [Bool.or_false, Nat.add_comm]

theorem run_chainStep_bind {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (position : GroupedBalancedSecurityGraph67.Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    run table exposed (chainStep exposed residual position query next) =
      (run table exposed (chainStep exposed residual position query
        (fun answer opened cache => .done (answer, opened, cache))) >>=
      fun first => compose first <$> run table first.value.2.1
        (next first.value.1 first.value.2.1 first.value.2.2)) := by
  unfold chainStep
  cases predEq : GroupedBalancedGraphMonitorPredecessor67.predecessor position.val with
  | none =>
      simp only [predEq]
      by_cases canonical : query = position.input []
      · simp only [if_pos canonical, run, pure_bind]
        exact (compose_clean _ _).symm
      · simp only [if_neg canonical]
        exact run_residualStep_bind table exposed residual query (.inl position) next
  | some previous =>
      simp only [predEq]
      cases parsed : parsedChainPayload position query with
      | none =>
          simp only [parsed]
          exact run_residualStep_bind table exposed residual query (.inl position) next
      | some point =>
          simp only [parsed]
          cases knownEq : exposed previous with
          | none =>
              simp only [knownEq, run, map_bind, bind_assoc]
              rw [run_residualStep_bind]
              simp only [map_bind, bind_map_left]
              simp only [addTest]
              apply bind_congr
              intro first
              simp only [Functor.map_map]
              congr 1
              funext second
              cases first
              cases second
              simp [compose, addTest, Bool.or_assoc, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm]
          | some known =>
              simp only [knownEq]
              by_cases canonical : point = truncate known
              · simp only [if_pos canonical, run, pure_bind]
                exact (compose_clean _ _).symm
              · simp only [if_neg canonical]
                exact run_residualStep_bind table exposed residual query (.inl position) next

theorem run_publicStep_bind {α : Type} (table : PointTable)
    (exposed : QueryCache PointSpec) (residual : QueryCache HashSpec)
    (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) :
    run table exposed (publicStep exposed residual query next) =
      (run table exposed (publicStep exposed residual query
        (fun answer opened cache => .done (answer, opened, cache))) >>=
      fun first => compose first <$> run table first.value.2.1
        (next first.value.1 first.value.2.1 first.value.2.2)) := by
  unfold publicStep
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [located]
      cases cached : residual query with
      | some answer =>
          simp only [cached, run, pure_bind]
          exact (compose_clean _ _).symm
      | none =>
          simp only [cached, run, bind_assoc, pure_bind]
          apply bind_congr
          intro answer
          exact (compose_clean _ _).symm
  | some position =>
      simp only [located]
      by_cases tagTwo : position.val.tag.val = 2
      · simp only [if_pos tagTwo]
        exact run_chainStep_bind table exposed residual position query next
      · simp only [if_neg tagTwo]
        rw [GroupedBalancedGraphMonitorSetup67.run_disclose,
          GroupedBalancedGraphMonitorSetup67.run_disclose]
        let opened := revealCache table (required position) exposed
        change run table opened
          (if query = position.input
            (GroupedBalancedGraphPayload67.payload
              (GroupedBalancedGraphMonitorTable67.privateOf (knownTable opened))
              (GroupedBalancedGraphMonitorTable67.labelsOf (knownTable opened))
              position)
          then .reveal (.inl position) (fun answer =>
            next answer (opened.cacheQuery (.inl position) answer) residual)
          else residualStep opened residual query (.inl position) next) = _
        split
        · simp only [run, pure_bind]
          exact (compose_clean _ _).symm
        · exact run_residualStep_bind table opened residual query (.inl position) next

#print axioms run_residualStep_bind
#print axioms run_publicStep_bind

end SigGolfCandidate.Hypertree.GroupedBalancedGraphRunBind67
end

/-! Erasing H5 trace marks from the joint interpreter yields the exact
class-metered passive graph execution, with its contact flag and test count. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointLocal67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexLift67
open GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexJoint67
open GroupedBalancedGraphIndexObserve67
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option maxHeartbeats 50000
open scoped Classical
attribute [local irreducible] SecurityIndexQuery.parse
  GroupedBalancedGraphQuery67.locate

theorem accumulate_compose {α β : Type} (bad : Bool) (tests : Nat)
    (first : Outcome α) (second : Outcome β) :
    accumulate bad tests (GroupedBalancedGraphRunBind67.compose first second) =
      accumulate (bad || first.bad) (tests + first.tests) second := by
  cases first
  cases second
  simp [accumulate, GroupedBalancedGraphRunBind67.compose,
    Bool.or_assoc, Nat.add_assoc]

theorem observe_ofGraphKeep {α β : Type} (table : PointTable)
    (cache : QueryCache PointSpec) (program : Program α)
    (next : Outcome α → SecurityIndexProgram.Program β) :
    observe (ofGraphKeep table cache program next) =
      run table cache program >>= fun result => observe (next result) := by
  unfold observe
  rw [execute_ofGraphKeep]
  simp only [map_bind]

theorem observe_cachedDraw {α : Type}
    (residual : QueryCache HashSpec) (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α) :
    observe (cachedDraw residual input mark next) =
      ((randomOracle (spec := HashSpec) input).run residual >>= fun result =>
        observe (next result.1 result.2)) := by
  cases cached : residual input with
  | some answer =>
      simp only [cachedDraw, cached, randomOracle.run_eq, pure_bind]
  | none =>
      simp only [cachedDraw, cached, observe_draw,
        randomOracle.run_eq, bind_assoc, pure_bind]


#print axioms observe_ofGraphKeep
#print axioms observe_cachedDraw

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointLocal67

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointObserve67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexLift67 GroupedBalancedGraphIndexKeep67
open GroupedBalancedGraphIndexJoint67 GroupedBalancedGraphIndexObserve67
open GroupedBalancedGraphIndexJointLocal67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
open scoped Classical
theorem done_step {α : Type} (table : PointTable) (value : α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat) :
    observe (compile table (.done value) remaining state graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.done value) remaining state graphCalls) := by
  change (pure (⟨⟨some value, remaining, state, graphCalls⟩,
      bad, tests⟩ : JointOutcome α) : ProbComp (JointOutcome α)) =
    accumulate bad tests <$>
      (pure (⟨⟨some value, remaining, state, graphCalls⟩,
        false, 0⟩ : JointOutcome α) : ProbComp (JointOutcome α))
  simp only [map_pure, accumulate, Bool.or_false, Nat.add_zero]

theorem coin_step {α : Type} (table : PointTable)
    (n : Nat) (next : Fin (n + 1) → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (ih : ∀ answer,
      observe (compile table (next answer) remaining state graphCalls
        signedMessages bad tests) =
      accumulate bad tests <$>
        run table state.exposed
          (GroupedBalancedGraphMetered67.limited
            (next answer) remaining state graphCalls)) :
    observe (compile table (.coin n next) remaining state graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.coin n next) remaining state graphCalls) := by
  change observe (.coin n (fun answer =>
      compile table (next answer) remaining state graphCalls
        signedMessages bad tests)) =
    accumulate bad tests <$> (($ᵗ Fin (n + 1)) >>= fun answer =>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (next answer) remaining state graphCalls))
  rw [observe_coin, map_bind]
  exact bind_congr ih

theorem sign_step {α : Type} (table : PointTable)
    (index : BitVec 160) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (ih : ∀ answer,
      observe (compile table (next answer) remaining
        (signed state index answer) graphCalls signedMessages bad tests) =
      accumulate bad tests <$>
        run table (signed state index answer).exposed
          (GroupedBalancedGraphMetered67.limited
            (next answer) remaining (signed state index answer) graphCalls)) :
    observe (compile table (.sign index next) remaining state graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.sign index next) remaining state graphCalls) := by
  change observe (compile table (next (table (.inr (.inl index)))) remaining
      (signed state index (table (.inr (.inl index)))) graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table (signed state index (table (.inr (.inl index)))).exposed
        (GroupedBalancedGraphMetered67.limited
          (next (table (.inr (.inl index)))) remaining
          (signed state index (table (.inr (.inl index)))) graphCalls)
  exact ih _

theorem private_step {α : Type} (table : PointTable)
    (input : Query) (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (ih : ∀ answer remaining state graphCalls signedMessages bad tests,
      observe (compile table (next answer) remaining state graphCalls
        signedMessages bad tests) =
      accumulate bad tests <$>
        run table state.exposed
          (GroupedBalancedGraphMetered67.limited
            (next answer) remaining state graphCalls)) :
    observe (compile table (.privateHash input outside next) remaining state
      graphCalls signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.privateHash input outside next) remaining state graphCalls) := by
  change observe (privateHashStepOn (SecurityIndexQuery.parse input)
      state input signedMessages
      (fun answer updated signedMessages =>
        compile table (next answer) remaining updated graphCalls
          signedMessages bad tests)) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.privateHash input outside next) remaining state graphCalls)
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      simp only [privateHashStepOn, parsed, observe_cachedDraw]
      cases cached : state.residual input with
      | some answer =>
          simp only [randomOracle.run_eq, cached, pure_bind,
            GroupedBalancedGraphMetered67.limited, run]
          exact ih answer remaining state graphCalls
            (insert pair.1 signedMessages) bad tests
      | none =>
          simp only [randomOracle.run_eq, cached, bind_assoc,
            GroupedBalancedGraphMetered67.limited, run, map_bind]
          apply bind_congr
          intro answer
          exact ih answer remaining
            (privateOpened state input answer) graphCalls
            (insert pair.1 signedMessages) bad tests
  | none =>
      simp only [privateHashStepOn, parsed, observe_unmarked]
      cases cached : state.residual input with
      | some answer =>
          simp only [randomOracle.run_eq, cached, pure_bind,
            GroupedBalancedGraphMetered67.limited, run]
          exact ih answer remaining state graphCalls
            signedMessages bad tests
      | none =>
          simp only [randomOracle.run_eq, cached, bind_assoc,
            GroupedBalancedGraphMetered67.limited, run, map_bind]
          apply bind_congr
          intro answer
          exact ih answer remaining
            (privateOpened state input answer) graphCalls
            signedMessages bad tests

theorem hash_zero_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat) :
    observe (compile table (.hash input next) 0 state graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.hash input next) 0 state graphCalls) := by
  change (pure (⟨⟨none, 0, state, graphCalls⟩,
      bad, tests⟩ : JointOutcome α) : ProbComp (JointOutcome α)) =
    accumulate bad tests <$>
      (pure (⟨⟨none, 0, state, graphCalls⟩,
        false, 0⟩ : JointOutcome α) : ProbComp (JointOutcome α))
  simp only [map_pure, accumulate, Bool.or_false, Nat.add_zero]

theorem hash_succ_step {α : Type} (table : PointTable)
    (input : Query) (next : BitVec 256 → View α)
    (remaining : Nat) (state : State) (graphCalls : Nat)
    (signedMessages : Finset Message) (bad : Bool) (tests : Nat)
    (ih : ∀ answer remaining state graphCalls signedMessages bad tests,
      observe (compile table (next answer) remaining state graphCalls
        signedMessages bad tests) =
      accumulate bad tests <$>
        run table state.exposed
          (GroupedBalancedGraphMetered67.limited
            (next answer) remaining state graphCalls)) :
    observe (compile table (.hash input next) (remaining + 1) state
      graphCalls signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.hash input next) (remaining + 1) state graphCalls) := by
  change observe (publicHashStepOn (SecurityIndexQuery.parse input)
      table state input graphCalls bad tests
      (fun answer updated graphCalls bad tests =>
        compile table (next answer) remaining updated graphCalls
          signedMessages bad tests)) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          (.hash input next) (remaining + 1) state graphCalls)
  cases parsed : SecurityIndexQuery.parse input with
  | some pair =>
      have outside : GroupedBalancedGraphQuery67.locate input = none := by
        have queryEq := (SecurityIndexQuery.parse_some_iff input pair).1 parsed
        rw [← queryEq]
        exact GroupedBalancedGraphHonestSignView67.locate_index_none
          pair.1 pair.2
      simp only [publicHashStepOn, parsed, observe_cachedDraw]
      cases cached : state.residual input with
      | some answer =>
          simp only [randomOracle.run_eq, cached, pure_bind,
            GroupedBalancedGraphMetered67.limited, outside,
            GroupedBalancedGraphMonitorOracle67.publicStep, run]
          exact ih answer remaining state graphCalls signedMessages bad tests
      | none =>
          simp only [randomOracle.run_eq, cached, bind_assoc,
            GroupedBalancedGraphMetered67.limited, outside,
            GroupedBalancedGraphMonitorOracle67.publicStep, run,
            map_bind]
          apply bind_congr
          intro answer
          exact ih answer remaining
            (opened state state.exposed
              (state.residual.cacheQuery input answer))
            graphCalls signedMessages bad tests
  | none =>
      cases located : GroupedBalancedGraphQuery67.locate input with
      | none =>
          simp only [publicHashStepOn, parsed, observe_ofGraphKeep,
            GroupedBalancedGraphMetered67.limited, located,
            map_bind]
          conv_rhs => arg 2; rw [GroupedBalancedGraphRunBind67.run_publicStep_bind]
          simp only [map_bind]
          apply bind_congr
          intro first
          simp only [Option.isSome_none, Bool.false_eq_true, if_false,
            Nat.add_zero]
          rw [ih first.value.1 remaining
            (opened state first.value.2.1 first.value.2.2)
            graphCalls signedMessages (bad || first.bad)
            (tests + first.tests)]
          simp only [Functor.map_map]
          have functionEq :
              (accumulate (bad || first.bad) (tests + first.tests) :
                Outcome (GroupedBalancedGraphMetered67.Result α) →
                  Outcome (GroupedBalancedGraphMetered67.Result α)) =
              (fun second : Outcome (GroupedBalancedGraphMetered67.Result α) =>
                accumulate bad tests
                  (GroupedBalancedGraphRunBind67.compose first second)) := by
            funext second
            exact (accumulate_compose bad tests first second).symm
          rw [functionEq]
          rfl
      | some position =>
          simp only [publicHashStepOn, parsed, observe_ofGraphKeep,
            GroupedBalancedGraphMetered67.limited, located,
            map_bind]
          conv_rhs => arg 2; rw [GroupedBalancedGraphRunBind67.run_publicStep_bind]
          simp only [map_bind]
          apply bind_congr
          intro first
          simp only [Option.isSome_some, if_pos rfl, if_true]
          rw [ih first.value.1 remaining
            (opened state first.value.2.1 first.value.2.2)
            (graphCalls + 1) signedMessages (bad || first.bad)
            (tests + first.tests)]
          simp only [Functor.map_map]
          have functionEq :
              (accumulate (bad || first.bad) (tests + first.tests) :
                Outcome (GroupedBalancedGraphMetered67.Result α) →
                  Outcome (GroupedBalancedGraphMetered67.Result α)) =
              (fun second : Outcome (GroupedBalancedGraphMetered67.Result α) =>
                accumulate bad tests
                  (GroupedBalancedGraphRunBind67.compose first second)) := by
            funext second
            exact (accumulate_compose bad tests first second).symm
          rw [functionEq]
          rfl

attribute [local irreducible] GroupedBalancedGraphIndexJoint67.compile
  GroupedBalancedGraphMetered67.limited SecurityIndexQuery.parse
  GroupedBalancedGraphQuery67.locate

theorem observe_compile {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) (state : State)
    (graphCalls : Nat) (signedMessages : Finset Message)
    (bad : Bool) (tests : Nat) :
    observe (compile table view remaining state graphCalls
      signedMessages bad tests) =
    accumulate bad tests <$>
      run table state.exposed
        (GroupedBalancedGraphMetered67.limited
          view remaining state graphCalls) := by
  induction view generalizing remaining state graphCalls signedMessages bad tests with
  | done value =>
      exact done_step table value remaining state graphCalls
        signedMessages bad tests
  | coin n next ih =>
      exact coin_step table n next remaining state graphCalls
        signedMessages bad tests
        (fun answer => ih answer remaining state graphCalls
          signedMessages bad tests)
  | sign index next ih =>
      exact sign_step table index next remaining state graphCalls
        signedMessages bad tests
        (fun answer => ih answer remaining (signed state index answer)
          graphCalls signedMessages bad tests)
  | privateHash input outside next ih =>
      exact private_step table input outside next remaining state graphCalls
        signedMessages bad tests ih
  | hash input next ih =>
      cases remaining with
      | zero =>
          exact hash_zero_step table input next state graphCalls
            signedMessages bad tests
      | succ remaining =>
          exact hash_succ_step table input next remaining state graphCalls
            signedMessages bad tests ih
#print axioms observe_compile

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointObserve67
