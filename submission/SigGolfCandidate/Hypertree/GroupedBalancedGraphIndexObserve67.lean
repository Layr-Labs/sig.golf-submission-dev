import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexProgram67

/-! Forgetting the H5 trace yields the exact planted direct67 interaction law.
The trace monitor is observational: neither its mark nor its collision flag is
returned to an adaptive adversary continuation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexObserve67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphIndexProgram67
open GroupedBalancedGraphIndexLift67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped Classical
attribute [local irreducible] SecurityIndexQuery.parse

noncomputable def observe {α : Type}
    (program : SecurityIndexProgram.Program α) : ProbComp α :=
  Prod.fst <$> SecurityIndexProgram.execute program

@[simp] theorem observe_pure {α : Type} (value : α) :
    observe (.pure value) = pure value := by
  simp [observe, SecurityIndexProgram.execute]

@[simp] theorem observe_coin {α : Type} (n : Nat)
    (next : Fin (n + 1) → SecurityIndexProgram.Program α) :
    observe (.coin n next) =
      (($ᵗ Fin (n + 1)) >>= fun answer => observe (next answer)) := by
  simp only [observe, SecurityIndexProgram.execute, map_bind]

@[simp] theorem observe_draw {α : Type} (mark : Bool)
    (next : BitVec 256 → SecurityIndexProgram.Program α) :
    observe (.draw mark next) =
      (($ᵗ BitVec 256) >>= fun answer => observe (next answer)) := by
  simp only [observe, SecurityIndexProgram.execute, map_bind,
    Functor.map_map]

theorem observe_unmarked {α β : Type} (program : ProbComp α)
    (next : α → SecurityIndexProgram.Program β) :
    observe (unmarked program next) =
      (program >>= fun value => observe (next value)) := by
  unfold observe
  rw [execute_unmarked, map_bind]

theorem observe_readIndex {α : Type} (state : State)
    (input : Query) (mark : Bool)
    (next : BitVec 256 → QueryCache HashSpec →
      SecurityIndexProgram.Program α) :
    observe (readIndex state input mark next) =
      ((randomOracle (spec := HashSpec) input).run state.residual >>=
        fun result => observe (next result.1 result.2)) := by
  cases cached : state.residual input with
  | some answer =>
      simp only [readIndex, cached, randomOracle.run_eq, pure_bind]
  | none =>
      simp only [readIndex, cached, observe_draw,
        randomOracle.run_eq, bind_assoc]
      simp only [pure_bind]

theorem parsed_canonical_none (table : PointTable) (query : Query)
    (pair : Message × Bytes 32)
    (parsed : SecurityIndexQuery.parse query = some pair) :
    GroupedBalancedGraphOracle67.canonical
      (GroupedBalancedGraphMonitorTable67.privateOf table)
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      query = none := by
  have queryEq := (SecurityIndexQuery.parse_some_iff query pair).1 parsed
  rw [← queryEq]
  simp only [GroupedBalancedGraphOracle67.canonical,
    GroupedBalancedGraphHonestSignView67.locate_index_none]

noncomputable def plainHashStepOn {α : Type}
    (parsed : Option (Message × Bytes 32)) (table : PointTable)
    (state : State) (input : Query)
    (next : BitVec 256 → State → ProbComp α) : ProbComp α := do
  let result ← (GroupedBalancedGraphOracle67.publicOracle
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) input).run
          state.residual
  let updated := match parsed with
    | some _ => state.recordIndex result.2
    | none => { state with residual := result.2 }
  next result.1 updated

noncomputable def plainHashStep {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (next : BitVec 256 → State → ProbComp α) : ProbComp α :=
  plainHashStepOn (SecurityIndexQuery.parse input) table state input next

noncomputable def plainSignStep {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (state : State) (message : Message)
    (next : GroupedBalancedScheme67.Signature → State → ProbComp α) :
    ProbComp α := do
  let randomizerResult ←
    (randomOracle (spec := HashSpec)
      (SecurityRandomOracle.randomizerInput secretKey message)).run
        state.residual
  let randomizer := randomizerResult.1
  let indexResult ←
    (randomOracle (spec := HashSpec)
      (SecurityRandomOracle.indexInput message randomizer)).run
        randomizerResult.2
  let index : BitVec 160 := indexResult.1.extractLsb' 0 160
  let bottomAnswer := table (.inr (.inl index))
  let signature :=
    GroupedBalancedGraphHonestSignView67.signatureFromAnswers
      setup randomizer index bottomAnswer
  next signature (state.recordSign message indexResult.2)

/-- Public hash uses the actual planted graph oracle. Honest signing uses the
same tag-6/tag-5 lazy residual oracle and exact structured direct67 signature. -/
noncomputable def plain {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec) :
    Interaction α → State → ProbComp (α × State)
  | .done value, state => pure (value, state)
  | .coin n next, state => do
      let answer ← $ᵗ Fin (n + 1)
      plain table secretKey setup (next answer) state
  | .hash input next, state =>
      plainHashStep table state input (fun answer updated =>
        plain table secretKey setup (next answer) updated)
  | .sign message next, state =>
      plainSignStep table secretKey setup state message
        (fun signature updated =>
          plain table secretKey setup (next signature) updated)

theorem observe_signStep {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (state : State) (message : Message)
    (next : GroupedBalancedScheme67.Signature → State →
      SecurityIndexProgram.Program α) :
    observe (signStep table secretKey setup state message next) =
      plainSignStep table secretKey setup state message
        (fun signature updated => observe (next signature updated)) := by
  simp only [signStep, plainSignStep, observe_unmarked]
  apply bind_congr
  intro randomizerResult
  simp only [observe_readIndex]

theorem observe_hashStepOn {α : Type}
    (table : PointTable)
    (state : State) (input : Query)
    (parsed : Option (Message × Bytes 32))
    (parsedEq : parsed = SecurityIndexQuery.parse input)
    (next : BitVec 256 → State → SecurityIndexProgram.Program α) :
    observe (hashStepOn parsed table state input next) =
      plainHashStepOn parsed table state input
        (fun answer updated => observe (next answer updated)) := by
  cases parsed with
  | none =>
      simp only [hashStepOn, plainHashStepOn, observe_unmarked]
  | some pair =>
      have canonical := parsed_canonical_none table input pair parsedEq.symm
      simp only [hashStepOn, plainHashStepOn,
        GroupedBalancedGraphOracle67.publicOracle, canonical,
        observe_readIndex]

theorem observe_hashStep {α : Type} (table : PointTable)
    (state : State) (input : Query)
    (next : BitVec 256 → State → SecurityIndexProgram.Program α) :
    observe (hashStep table state input next) =
      plainHashStep table state input
        (fun answer updated => observe (next answer updated)) := by
  exact observe_hashStepOn table state input (SecurityIndexQuery.parse input) rfl next

theorem observe_compile_coin {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (n : Nat) (next : Fin (n + 1) → Interaction α) (state : State)
    (ih : ∀ answer,
      observe (compile table secretKey setup (next answer) state) =
        plain table secretKey setup (next answer) state) :
    observe (compile table secretKey setup (.coin n next) state) =
      plain table secretKey setup (.coin n next) state := by
  change observe (.coin n (fun answer =>
      compile table secretKey setup (next answer) state)) =
    (($ᵗ Fin (n + 1)) >>= fun answer =>
      plain table secretKey setup (next answer) state)
  rw [observe_coin]
  exact bind_congr ih

theorem plainHashStep_congr {α : Type} (table : PointTable)
    (state : State) (input : Query) (first second : BitVec 256 → State → ProbComp α)
    (same : ∀ answer updated, first answer updated = second answer updated) :
    plainHashStep table state input first = plainHashStep table state input second := by
  unfold plainHashStep plainHashStepOn
  apply bind_congr
  intro result
  exact same result.1 _

theorem plainSignStep_congr {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (state : State) (message : Message)
    (first second : GroupedBalancedScheme67.Signature → State → ProbComp α)
    (same : ∀ signature updated, first signature updated = second signature updated) :
    plainSignStep table secretKey setup state message first =
      plainSignStep table secretKey setup state message second := by
  unfold plainSignStep
  apply bind_congr
  intro randomizerResult
  apply bind_congr
  intro indexResult
  exact same _ _

theorem observe_compile {α : Type} (table : PointTable)
    (secretKey : SecretKey) (setup : QueryCache PointSpec)
    (interaction : Interaction α) (state : State) :
    observe (compile table secretKey setup interaction state) =
      plain table secretKey setup interaction state := by
  induction interaction generalizing state with
  | done value => simp only [compile, plain, observe_pure]
  | coin n next ih =>
      exact observe_compile_coin table secretKey setup n next state
        (fun answer => ih answer state)
  | hash input next ih =>
      change observe (hashStep table state input (fun answer updated =>
        compile table secretKey setup (next answer) updated)) =
        plainHashStep table state input (fun answer updated =>
          plain table secretKey setup (next answer) updated)
      rw [observe_hashStep]
      exact plainHashStep_congr table state input _ _ (fun answer updated =>
        ih answer updated)
  | sign message next ih =>
      change observe (signStep table secretKey setup state message
        (fun signature updated =>
          compile table secretKey setup (next signature) updated)) =
        plainSignStep table secretKey setup state message
          (fun signature updated =>
            plain table secretKey setup (next signature) updated)
      rw [observe_signStep]
      exact plainSignStep_congr table secretKey setup state message _ _
        (fun signature updated => ih signature updated)

#print axioms observe_compile

theorem observe_start {α : Type} (table : PointTable)
    (secretKey : SecretKey) (interaction : Interaction α) :
    observe (start table secretKey interaction) =
      plain table secretKey (GroupedBalancedGraphMonitorSetup67.cache table)
        interaction {} :=
  observe_compile table secretKey
    (GroupedBalancedGraphMonitorSetup67.cache table) interaction {}

end SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexObserve67
