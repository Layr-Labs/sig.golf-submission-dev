import SigGolfCandidate.Hypertree.GroupedBalancedGraphIndexJointTotalView67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteraction67
import SigGolfCandidate.Hypertree.SecurityGameHop

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphViewWorld67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67. -/
section
/-! Reify the structured organizer View as an ordinary World oracle program.
The total View cutoff is exactly the general hash-query cutoff of that program,
retaining the unused budget in its result. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphViewWorld67
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorSignCompiler67
open GroupedBalancedGraphIndexJointTotalView67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def ofView {α : Type} (table : PointTable) : View α → OracleComp World α
  | .done value => pure value
  | .coin n next => do
      let answer ← liftM (World.query (.inl n))
      ofView table (next answer)
  | .sign index next =>
      ofView table (next (table (.inr (.inl index))))
  | .hash input next => do
      let answer ← liftM (World.query (.inr input))
      ofView table (next answer)
  | .privateHash input _ next => do
      let answer ← liftM (World.query (.inr input))
      ofView table (next answer)

def hashCharge : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

noncomputable def cutoffWithRemaining {α : Type}
    (program : OracleComp World α) :
    Nat → OracleComp World (Option α × Nat) :=
  OracleComp.construct
    (fun value remaining => pure (some value, remaining))
    (fun query _ next remaining =>
      if hashCharge query ≤ remaining then do
        let answer ← liftM (World.query query)
        next answer (remaining - hashCharge query)
      else pure (none, remaining)) program

@[simp] theorem cutoff_pure {α : Type} (value : α) (remaining : Nat) :
    cutoffWithRemaining (pure value : OracleComp World α) remaining =
      pure (some value, remaining) := rfl

theorem cutoff_query_bind {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (remaining : Nat) :
    cutoffWithRemaining (liftM (World.query query) >>= next) remaining =
      if hashCharge query ≤ remaining then do
        let answer ← liftM (World.query query)
        cutoffWithRemaining (next answer) (remaining - hashCharge query)
      else pure (none, remaining) := rfl

theorem ofView_totalLimited {α : Type} (table : PointTable)
    (view : View α) (remaining : Nat) :
    ofView table (totalLimited view remaining) =
      cutoffWithRemaining (ofView table view) remaining := by
  induction view generalizing remaining with
  | done value => rfl
  | coin n next ih =>
      simp only [totalLimited, ofView, cutoff_query_bind, hashCharge,
        Nat.zero_le, if_pos, Nat.sub_zero]
      exact bind_congr (fun answer => ih answer remaining)
  | sign index next ih =>
      exact ih (table (.inr (.inl index))) remaining
  | hash input next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [totalLimited, ofView, cutoff_query_bind, hashCharge,
            Nat.add_le_add_iff_right, zero_le, if_pos,
            Nat.add_sub_cancel_left]
          exact bind_congr (fun answer => ih answer remaining)
  | privateHash input outside next ih =>
      cases remaining with
      | zero => rfl
      | succ remaining =>
          simp only [totalLimited, ofView, cutoff_query_bind, hashCharge,
            Nat.add_le_add_iff_right, zero_le, if_pos,
            Nat.add_sub_cancel_left]
          exact bind_congr (fun answer => ih answer remaining)

def counted {α : Type} (program : OracleComp World α) :
    OracleComp World (α × Nat) :=
  OracleComp.construct (fun value => pure (value, 0))
    (fun query _ next => do
      let answer ← liftM (World.query query)
      let result ← next answer
      pure (result.1, result.2 + hashCharge query)) program

@[simp] theorem counted_pure {α : Type} (value : α) :
    counted (pure value : OracleComp World α) = pure (value, 0) := rfl

theorem counted_query_bind {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    counted (liftM (World.query query) >>= next) = (do
      let answer ← liftM (World.query query)
      let result ← counted (next answer)
      pure (result.1, result.2 + hashCharge query)) := rfl

private theorem run'_query_bind {σ α : Type}
    (implementation : QueryImpl World (StateT σ ProbComp))
    (query : World.Domain)
    (next : World.Range query → OracleComp World α) (cache : σ) :
    (simulateQ implementation (liftM (World.query query) >>= next)).run' cache =
      ((implementation query).run cache >>= fun result =>
        (simulateQ implementation (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]

/-- The structured View's total cutoff uses exactly the same hash-call
semantics as the ordinary counted World program. -/
theorem prob_cutoff_eq_counted {σ α : Type}
    (implementation : QueryImpl World (StateT σ ProbComp))
    (program : OracleComp World α) (cache : σ)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => ∃ value, result.1 = some value ∧ event value |
      (simulateQ implementation
        (cutoffWithRemaining program budget)).run' cache] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ implementation (counted program)).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      letI : DecidablePred (fun result : Option α × Nat =>
          ∃ output, result.1 = some output ∧ event output) :=
        fun _ => Classical.propDecidable _
      letI : DecidablePred (fun result : α × Nat =>
          event result.1 ∧ result.2 ≤ budget) :=
        fun _ => Classical.propDecidable _
      simp only [cutoff_pure, counted_pure, simulateQ_pure,
        StateT.run'_eq, StateT.run_pure, map_pure, probEvent_pure,
        Prod.fst, Prod.snd, Option.some.injEq, Nat.zero_le,
        and_true, exists_eq_left]
      have eventEq : (∃ output : α,
          some value = some output ∧ event output) ↔ event value := by
        constructor
        · rintro ⟨output, same, accepted⟩
          cases Option.some.inj same
          exact accepted
        · intro accepted
          exact ⟨value, rfl, accepted⟩
      by_cases accepted : event value
      · have left : ∃ output : α,
            some value = some output ∧ event output := eventEq.mpr accepted
        have right : event value ∧ 0 ≤ budget :=
          ⟨accepted, Nat.zero_le _⟩
        simp only [if_pos left, if_pos right]
      · have left : ¬∃ output : α,
            some value = some output ∧ event output :=
          fun candidate => accepted (eventEq.mp candidate)
        have right : ¬(event value ∧ 0 ≤ budget) :=
          fun candidate => accepted candidate.1
        simp only [if_neg left, if_neg right]
  | query_bind query next ih =>
      rw [cutoff_query_bind, counted_query_bind]
      by_cases allowed : hashCharge query ≤ budget
      · rw [if_pos allowed, run'_query_bind, run'_query_bind]
        simp only [probEvent_bind_eq_tsum]
        apply tsum_congr
        intro step
        rw [ih step.1 step.2 (budget - hashCharge query)]
        congr 1
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq,
          StateT.run_map, Functor.map_map, probEvent_map, Function.comp_def]
        apply probEvent_congr' _ rfl
        intro result _
        have arithmetic : result.1.2 ≤ budget - hashCharge query ↔
            result.1.2 + hashCharge query ≤ budget := by omega
        exact and_congr_right fun _ => arithmetic
      · rw [if_neg allowed, run'_query_bind]
        have exceeded (count : Nat) :
            ¬count + hashCharge query ≤ budget := by omega
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq,
          StateT.run_map, Functor.map_map, probEvent_bind_eq_tsum,
          probEvent_map, Function.comp_def, exceeded]

/-- A completed bounded organizer View is exactly the completion event of
the same unrestricted World program with at most `budget` hash calls. -/
theorem prob_ofView_limited_eq_counted {σ α : Type}
    (implementation : QueryImpl World (StateT σ ProbComp))
    (table : PointTable) (view : View α) (cache : σ)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => ∃ value, result.1 = some value ∧ event value |
      (simulateQ implementation
        (ofView table (totalLimited view budget))).run' cache] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget |
      (simulateQ implementation
        (counted (ofView table view))).run' cache] := by
  rw [ofView_totalLimited]
  exact prob_cutoff_eq_counted implementation _ cache budget event

#print axioms ofView_totalLimited
#print axioms prob_cutoff_eq_counted
#print axioms prob_ofView_limited_eq_counted

end SigGolfCandidate.Hypertree.GroupedBalancedGraphViewWorld67

end

/-! A secret-key-independent GameWorld program for the abstract direct67
interaction. Honest randomizer calls use the typed old private slot; the H5
index call and attacker/verifier calls use the public oracle port. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphInteraction67
open GroupedBalancedGraphViewWorld67
open GroupedBalancedGraphHonestSignView67
open SecurityDerivation SecurityGameHop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

def translate (secretKey : SecretKey) :
    QueryImpl GameWorld (OracleComp World) :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := OracleComp World) +
    fun query => (SecurityDerivation.realImplementation secretKey query).liftComp World

abbrev resolve {α : Type} (secretKey : SecretKey)
    (program : OracleComp GameWorld α) : OracleComp World α :=
  simulateQ (translate secretKey) program

def gameView {α : Type} (table : PointTable)
    (cache : QueryCache PointSpec) :
    Interaction α → OracleComp GameWorld α
  | .done value => pure value
  | .coin n next => do
      let answer ← liftM (GameWorld.query (.inl n))
      gameView table cache (next answer)
  | .hash input next => do
      let answer ← liftM (GameWorld.query (.inr (.inr input)))
      gameView table cache (next answer)
  | .sign message next => do
      let randomizer ← liftM
        (GameWorld.query (.inr (.inl (.randomizer message))))
      let indexAnswer ← liftM
        (GameWorld.query (.inr (.inr
          (SecurityRandomOracle.indexInput message randomizer))))
      let index : BitVec 160 := indexAnswer.extractLsb' 0 160
      let signature := signatureFromAnswers cache randomizer index
        (table (.inr (.inl index)))
      gameView table cache (next signature)

theorem resolve_coin (secretKey : SecretKey) (n : Nat) :
    resolve secretKey
      (liftM (GameWorld.query (.inl n))) =
      liftM (World.query (.inl n)) := by
  rfl

theorem resolve_public (secretKey : SecretKey) (input : Query) :
    resolve secretKey
      (liftM (GameWorld.query (.inr (.inr input)))) =
      liftM (World.query (.inr input)) := by
  rfl

theorem resolve_randomizer (secretKey : SecretKey)
    (message : Message) :
    resolve secretKey
      (liftM (GameWorld.query
        (.inr (.inl (.randomizer message))))) =
      liftM (World.query (.inr
        (SecurityRandomOracle.randomizerInput secretKey message))) := by
  rfl

theorem resolve_gameView {α : Type}
    (secretKey : SecretKey) (table : PointTable)
    (cache : QueryCache PointSpec) (interaction : Interaction α) :
    resolve secretKey
      (gameView table cache interaction) =
    ofView table (toView secretKey cache interaction) := by
  induction interaction with
  | done value => rfl
  | coin n next ih =>
      simp only [gameView, toView, ofView,
        resolve, simulateQ_bind,
        simulateQ_pure, resolve_coin]
      exact bind_congr ih
  | hash input next ih =>
      simp only [gameView, toView, ofView,
        resolve, simulateQ_bind,
        simulateQ_pure, resolve_public]
      exact bind_congr ih
  | sign message next ih =>
      simp only [gameView, toView, honestSign, ofView,
        resolve, simulateQ_bind,
        simulateQ_pure, resolve_randomizer, resolve_public]
      apply bind_congr
      intro randomizer
      apply bind_congr
      intro indexAnswer
      exact ih _

#print axioms resolve_gameView

end SigGolfCandidate.Hypertree.GroupedBalancedGameWorld67
