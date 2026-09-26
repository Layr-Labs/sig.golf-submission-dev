import SigGolfCandidate.Hypertree.GroupedBalancedResidualNoPrivate67

/-! Successful eager organizer hash and signing steps expose their exact
continuation and action-log prefixes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedEagerDecompose67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphMonitorSignCoupling67
open GroupedBalancedGraphHonestSignView67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGameQueryTrace67
open GroupedBalancedGameViewLoggedBridge67
open GroupedBalancedIdealEagerCutoff67
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem private_step_present {α : Type} (table : PointTable)
    (input : Query)
    (outside : GroupedBalancedGraphQuery67.locate input = none)
    (next : BitVec 256 → View α) (remaining : Nat)
    (state : State) (target : Option (Option α × Nat × State))
    (member : target ∈ support
      (execute table (.privateHash input outside next) remaining state)) :
    ∃ answer nextState,
      target ∈ support (execute table (next answer) remaining nextState) ∧
      nextState.residual input = some answer ∧
      (nextState = state ∨ nextState = privateOpened state input answer) := by
  cases present : state.residual input with
  | some answer =>
      exact ⟨answer, state, by simpa only [execute, present] using member,
        present, Or.inl rfl⟩
  | none =>
      simp only [execute, present, mem_support_bind_iff] at member
      obtain ⟨answer, _, tail⟩ := member
      exact ⟨answer, privateOpened state input answer, tail,
        QueryCache.cacheQuery_self .., Or.inr rfl⟩

theorem sign_successor {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable) (table : PointTable)
    (cache : QueryCache PointSpec) (message : Message)
    (next : GroupedBalancedScheme67.Signature →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache (.sign message next)
          (budget + 1 + 1)) remaining state)) :
    ∃ indexAnswer state' tailTrace,
      let randomizer := answers (.randomizer message)
      let input := SecurityRandomOracle.indexInput message randomizer
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let bottomAnswer := table (.inr (.inl index))
      trace = .privateHash :: .publicHash input :: tailTrace ∧
      state'.residual input = some indexAnswer ∧
      (state' = state ∨ state' = privateOpened state input indexAnswer) ∧
      some (some (value, tailTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache
            (next (signatureFromAnswers cache randomizer index bottomAnswer))
            budget) remaining
          (signed state' index bottomAnswer)) := by
  let randomizer := answers (.randomizer message)
  let input := SecurityRandomOracle.indexInput message randomizer
  let branch : View (Option α × List Action) :=
    .privateHash input (locate_index_none message randomizer)
      (fun indexAnswer =>
        let index : BitVec 160 := indexAnswer.extractLsb' 0 160
        .sign index (fun bottomAnswer =>
          prependAction (.publicHash input)
            (eagerCutoffView answers cache
              (next (signatureFromAnswers cache randomizer index bottomAnswer))
              budget)))
  have unfolded : eagerCutoffView answers cache
      (.sign message next) (budget + 1 + 1) =
      prependAction .privateHash branch := by
    rfl
  obtain ⟨trace', firstEq, firstMember⟩ :=
    GroupedBalancedResidualNoPrivate67.prepend_decompose
      table .privateHash branch remaining state final value trace left
      (by simpa only [unfolded] using member)
  obtain ⟨indexAnswer, state', secondMember, present, shape⟩ :=
    private_step_present table input (locate_index_none message randomizer)
      (fun indexAnswer =>
        let index : BitVec 160 := indexAnswer.extractLsb' 0 160
        .sign index (fun bottomAnswer =>
          prependAction (.publicHash input)
            (eagerCutoffView answers cache
              (next (signatureFromAnswers cache randomizer index bottomAnswer))
              budget))) remaining state _
      (by simpa only [branch] using firstMember)
  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
  let bottomAnswer := table (.inr (.inl index))
  have thirdMember : some (some (value, trace'), left, final) ∈ support
      (execute table
        (prependAction (.publicHash input)
          (eagerCutoffView answers cache
            (next (signatureFromAnswers cache randomizer index bottomAnswer))
            budget)) remaining (signed state' index bottomAnswer)) := by
    simpa only [execute] using secondMember
  obtain ⟨tailTrace, secondEq, tailMember⟩ :=
    GroupedBalancedResidualNoPrivate67.prepend_decompose table
      (.publicHash input)
      (eagerCutoffView answers cache
        (next (signatureFromAnswers cache randomizer index bottomAnswer)) budget)
      remaining (signed state' index bottomAnswer)
      final value trace' left thirdMember
  exact ⟨indexAnswer, state', tailTrace, by rw [firstEq, secondEq],
    present, shape, tailMember⟩

theorem sign_successor_safe {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable) (table : PointTable)
    (cache : QueryCache PointSpec) (message : Message)
    (next : GroupedBalancedScheme67.Signature →
      GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (initial : GroupedBalancedGraphMonitorInvariant67.Safe table
      state.signedBottom state.exposed state.residual)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache (.sign message next)
          (budget + 1 + 1)) remaining state)) :
    ∃ indexAnswer state' tailTrace,
      let randomizer := answers (.randomizer message)
      let input := SecurityRandomOracle.indexInput message randomizer
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let bottomAnswer := table (.inr (.inl index))
      trace = .privateHash :: .publicHash input :: tailTrace ∧
      state'.residual input = some indexAnswer ∧
      state'.signedBottom = state.signedBottom ∧
      GroupedBalancedGraphMonitorInvariant67.Safe table
        (signed state' index bottomAnswer).signedBottom
        (signed state' index bottomAnswer).exposed
        (signed state' index bottomAnswer).residual ∧
      some (some (value, tailTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache
            (next (signatureFromAnswers cache randomizer index bottomAnswer))
            budget) remaining
          (signed state' index bottomAnswer)) := by
  obtain ⟨indexAnswer, state', tailTrace, traceEq, present,
    shape, tailMember⟩ :=
    sign_successor answers table cache message next budget remaining
      state final value trace left member
  let randomizer := answers (.randomizer message)
  let input := SecurityRandomOracle.indexInput message randomizer
  let index : BitVec 160 := indexAnswer.extractLsb' 0 160
  let bottomAnswer := table (.inr (.inl index))
  have stateSafe : GroupedBalancedGraphMonitorInvariant67.Safe table
      state'.signedBottom state'.exposed state'.residual := by
    rcases shape with same | same
    · subst state'
      exact initial
    · subst state'
      refine ⟨initial.1, initial.2.1, ?_⟩
      apply GroupedBalancedGraphMonitorInvariant67.ResidualSafe.cacheQuery
        table state.residual initial.2.2 input indexAnswer
      intro position located
      rw [locate_index_none message randomizer] at located
      cases located
  have signedSafe :=
    GroupedBalancedGraphSignExposure67.safe_reveal_bottom
      table state'.signedBottom state'.exposed state'.residual
      stateSafe index
  have signedEq : state'.signedBottom = state.signedBottom := by
    rcases shape with same | same <;> subst state' <;> rfl
  exact ⟨indexAnswer, state', tailTrace, traceEq,
    present, signedEq, signedSafe, tailMember⟩

theorem hash_successor {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable) (table : PointTable)
    (cache : QueryCache PointSpec) (input : Query)
    (next : BitVec 256 → GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache (.hash input next) (budget + 1))
        (remaining + 1) state)) :
    ∃ answer state' tailTrace,
      trace = .publicHash input :: tailTrace ∧
      some (some (value, tailTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache (next answer) budget)
          remaining state') := by
  obtain ⟨answer, state', inner, _⟩ :=
    GroupedBalancedResidualNoPrivate67.hash_step table input input
      (fun answer => prependAction (.publicHash input)
        (eagerCutoffView answers cache (next answer) budget))
      remaining state final (value, trace) left
      (by simpa only [eagerCutoffView] using member)
  obtain ⟨tailTrace, traceEq, tailMember⟩ :=
    GroupedBalancedResidualNoPrivate67.prepend_decompose
      table (.publicHash input)
      (eagerCutoffView answers cache (next answer) budget)
      remaining state' final value trace left inner
  exact ⟨answer, state', tailTrace, traceEq, tailMember⟩

theorem hash_successor_safe {α : Type}
    (answers : SecurityGraphIdeal.PrivateTable) (table : PointTable)
    (cache : QueryCache PointSpec) (input : Query)
    (next : BitVec 256 → GroupedBalancedGraphInteraction67.Interaction α)
    (budget remaining : Nat) (state final : State)
    (initial : GroupedBalancedGraphMonitorInvariant67.Safe table
      state.signedBottom state.exposed state.residual)
    (value : Option α) (trace : List Action) (left : Nat)
    (member : some (some (value, trace), left, final) ∈ support
      (execute table
        (eagerCutoffView answers cache (.hash input next) (budget + 1))
        (remaining + 1) state)) :
    ∃ answer state' tailTrace,
      trace = .publicHash input :: tailTrace ∧
      state'.signedBottom = state.signedBottom ∧
      GroupedBalancedGraphMonitorInvariant67.Safe table
        state'.signedBottom state'.exposed state'.residual ∧
      some (some (value, tailTrace), left, final) ∈ support
        (execute table
          (eagerCutoffView answers cache (next answer) budget)
          remaining state') := by
  have queryMember : some (some (value, trace), left, final) ∈ support
      (execute table
        (.hash input (fun answer => prependAction (.publicHash input)
          (eagerCutoffView answers cache (next answer) budget)))
        (remaining + 1) state) := by
    simpa only [eagerCutoffView] using member
  simp only [execute] at queryMember
  by_cases first : GroupedBalancedGraphMonitorPublicCoupling67.inputHit
      table state.exposed input
  · simp only [if_pos first, support_pure,
      Set.mem_singleton_iff, Option.some_ne_none] at queryMember
  · simp only [if_neg first, mem_support_bind_iff] at queryMember
    obtain ⟨read, readMember, tail⟩ := queryMember
    by_cases second : GroupedBalancedGraphMonitorPublicCoupling67.outputHit
        table input read.1
    · simp only [if_pos second, support_pure,
        Set.mem_singleton_iff, Option.some_ne_none] at tail
    · simp only [if_neg second] at tail
      let exposed := GroupedBalancedGraphMonitorPublicCoupling67.opened
        table state.exposed input
      let nextState := opened state exposed read.2
      have readSupported :=
        GroupedBalancedGraphMonitorCompileCoupling67.read_supported
          table state.signedBottom state.exposed state.residual initial
          input read readMember first second
      have safeRead :=
        GroupedBalancedGraphMonitorPublicUnified67.public_read_safe
          table state.signedBottom state.exposed state.residual initial
          input (read.1, exposed, read.2) readSupported
      obtain ⟨tailTrace, traceEq, child⟩ :=
        GroupedBalancedResidualNoPrivate67.prepend_decompose
          table (.publicHash input)
          (eagerCutoffView answers cache (next read.1) budget)
          remaining nextState final value trace left
          (by simpa only [nextState] using tail)
      exact ⟨read.1, nextState, tailTrace, traceEq, rfl,
        by simpa only [nextState, opened] using safeRead, child⟩

#print axioms private_step_present
#print axioms sign_successor
#print axioms hash_successor
#print axioms hash_successor_safe

end SigGolfCandidate.Hypertree.GroupedBalancedEagerDecompose67
