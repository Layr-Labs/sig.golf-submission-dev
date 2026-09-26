import SigGolfCandidate.Hypertree.SecurityMonitorGraphView
import SigGolfCandidate.Hypertree.SecurityGraphMonitorReturns
import SigGolfCandidate.Hypertree.SecurityMonitorViewBounds
import SigGolfCandidate.Hypertree.SecurityMonitorIndexInvariant

/-! Inlined from SigGolfCandidate.Hypertree.SecurityMonitorGraphBudget; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorGraphLifetime. -/
section
namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphBudget
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityMonitorView SecurityMonitorIndexState
  SecurityMonitorGraphView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

theorem returns_mono {α : Type} (program : Program α) (first second : α → Prop)
    (implies : ∀ value, first value → second value) (all : AllReturns first program) :
    AllReturns second program := by
  induction program with
  | done value => exact implies value all
  | guess point value next ih => exact ih all
  | reveal point next ih | coin n next ih | bits next ih | collision target next ih =>
    exact fun answer => ih answer (all answer)

theorem indexStep_returns {α : Type} (property : α → Prop) (cache : QueryCache HashSpec)
    (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α)
    (all : ∀ answer residual, AllReturns property (next answer residual)) :
    AllReturns property (indexStep cache query next) := by
  unfold indexStep
  cases cache query with
  | some answer => exact all answer cache
  | none => exact fun answer => all answer _

/-- Exact conservation on every passive path. The equality also holds after
contacts: monitors never feed their flags back into public control flow. -/
theorem compile_conserved {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) :
    AllReturns (fun result : Result α => result.history.counts.total + result.remaining =
      history.counts.total + remaining) (compile nonces metadata view remaining exposed cache history) := by
  induction view generalizing remaining exposed cache history with
  | done value => exact rfl
  | coin n next ih => exact fun answer => ih answer remaining exposed cache history
  | hash query next ih =>
    cases remaining with
    | zero => exact rfl
    | succ remaining =>
      apply publicStep_returns
      intro answer opened residual
      apply returns_mono _ _ _ _ (ih answer remaining opened residual (recordPublic history query (cache query).isSome answer))
      intro result conserved
      rw [public_total] at conserved
      omega
  | sign message next ih =>
    unfold compile
    split
    next enough =>
      apply indexStep_returns
      intro answer residual
      apply disclose_returns
      intro opened
      apply returns_mono _ _ _ _ (ih _ (remaining - 117508) opened residual
        (recordSign history message (cache (SecurityRandomOracle.indexInput message (nonces message))).isSome answer))
      intro result conserved
      rw [sign_total] at conserved
      omega
    next short => exact rfl

/-- Setup's 739 calls share the same conserved budget as the full adversary view. -/
theorem start_conserved {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) :
    AllReturns (fun result : Result α => result.history.counts.total + result.remaining = budget)
      (start nonces metadata view budget) := by
  unfold start
  split
  next enough =>
    apply disclose_returns
    intro exposed
    apply returns_mono _ _ _ _ (compile_conserved nonces metadata view (budget - 739) exposed ∅ (recordKeygen {}))
    intro result conserved
    rw [keygen_total] at conserved
    change result.history.counts.total + result.remaining = (0 + 739) + (budget - 739) at conserved
    omega
  next short =>
    change 0 + budget = budget
    omega

/-- Support-wise charged-call bound in the same uniform point-table experiment
used by the graph hazard bound. No expectation changes worlds here. -/
theorem start_count_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) (result : Outcome (Result α))
    (member : result ∈ support (SecurityGraphMonitorProgram.experiment (start nonces metadata view budget) ∅)) :
    result.value.history.counts.total ≤ budget := by
  rw [SecurityGraphMonitorProgram.experiment, mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  have conserved := run_returns _ _ (start_conserved nonces metadata view budget) _ _ result member
  omega

/-- The actual common passive experiment satisfies the organizer's shared total
H-call cutoff on every path, across setup, signing, public probes, and verification. -/
theorem experiment_count_le (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : Outcome (Result SecurityExperiment.Result))
    (member : result ∈ support (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)) :
    result.value.history.counts.total ≤ budget := by
  unfold SecurityMonitorGraphView.experiment at member
  rw [mem_support_bind_iff] at member
  obtain ⟨nonces, _, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨metadata, _, member⟩ := member
  exact start_count_le nonces metadata _ budget result member

end SigGolfCandidate.Hypertree.SecurityMonitorGraphBudget

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphLifetime
open SigGolf OracleComp OracleSpec Reference SecurityGraphPassive SecurityGraphFactor
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityMonitorView SecurityMonitorIndexState
  SecurityMonitorIndexInvariant SecurityMonitorGraphView SecurityMonitorGraphBudget
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.constructorNameAsVariable false

/-- The common compiler preserves bookkeeping bounds even after a passive hit. -/
theorem compile_wellCounted {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) (counted : WellCounted history) :
    AllReturns (fun result : Result α => WellCounted result.history)
      (compile nonces metadata view remaining exposed cache history) := by
  induction view generalizing remaining exposed cache history with
  | done value => exact counted
  | coin n next ih => exact fun answer => ih answer remaining exposed cache history counted
  | hash query next ih =>
    cases remaining with
    | zero => exact counted
    | succ remaining =>
      apply publicStep_returns
      intro answer opened residual
      exact ih answer remaining opened residual _ (counted.recordPublic query _ answer)
  | sign message next ih =>
    unfold compile
    split
    · apply indexStep_returns
      intro answer residual
      apply disclose_returns
      intro opened
      exact ih _ (remaining - 117508) opened residual _ (counted.recordSign message _ answer)
    · exact counted

/-- At most one new signed message is inserted per actual signing operation. -/
theorem compile_signed_card {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (signs : Nat) (within : WithinSigns signs view)
    (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (history : History) :
    AllReturns (fun result : Result α => result.history.signedMessages.card ≤ history.signedMessages.card + signs)
      (compile nonces metadata view remaining exposed cache history) := by
  induction view generalizing signs remaining exposed cache history with
  | done value => exact Nat.le_add_right _ _
  | coin n next ih => exact fun answer => ih answer signs (within answer) remaining exposed cache history
  | hash query next ih =>
    cases remaining with
    | zero => exact Nat.le_add_right _ _
    | succ remaining =>
      apply publicStep_returns
      intro answer opened residual
      have later := ih answer signs (within answer) remaining opened residual
        (recordPublic history query (cache query).isSome answer)
      simpa only [public_messages] using later
  | sign message next ih =>
    unfold compile
    split
    next enough =>
      apply indexStep_returns
      intro answer residual
      apply disclose_returns
      intro opened
      apply returns_mono _ _ _ _ (ih _ (signs - 1) (within.2 _) (remaining - 117508) opened residual
        (recordSign history message (cache (SecurityRandomOracle.indexInput message (nonces message))).isSome answer))
      intro result limited
      change result.history.signedMessages.card ≤ (insert message history.signedMessages).card + (signs - 1) at limited
      have inserted := Finset.card_insert_le message history.signedMessages
      have positive := within.1
      omega
    next short => exact Nat.le_add_right _ _

theorem start_wellCounted {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) :
    AllReturns (fun result : Result α => WellCounted result.history) (start nonces metadata view budget) := by
  unfold start
  split
  · apply disclose_returns
    intro exposed
    exact compile_wellCounted nonces metadata view (budget - 739) exposed ∅ _ wellCounted_empty.recordKeygen
  · exact wellCounted_empty

theorem start_signed_card {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (signs : Nat) (within : WithinSigns signs view) (budget : Nat) :
    AllReturns (fun result : Result α => result.history.signedMessages.card ≤ signs)
      (start nonces metadata view budget) := by
  unfold start
  split
  · apply disclose_returns
    intro exposed
    have bound := compile_signed_card nonces metadata view signs within (budget - 739) exposed ∅ (recordKeygen {})
    simpa only [recordKeygen, Finset.card_empty, Nat.zero_add] using bound
  · exact Nat.zero_le _

/-- The fully concrete common experiment respects both the lifetime cap and
all trace-to-charged-count inequalities used by the probability monitors. -/
theorem experiment_history (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : Outcome (Result SecurityExperiment.Result))
    (member : result ∈ support (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)) :
    WellCounted result.value.history ∧ result.value.history.signedMessages.card ≤ LIFETIME := by
  unfold SecurityMonitorGraphView.experiment at member
  rw [mem_support_bind_iff] at member
  obtain ⟨nonces, _, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨metadata, _, member⟩ := member
  rw [SecurityGraphMonitorProgram.experiment, mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  refine ⟨run_returns _ _ (start_wellCounted nonces metadata _ budget) _ _ result member, ?_⟩
  have within := ofInteract_withinSigns adversary (truncate (metadata (.node 159 0))) rounds
    (adversary.initial (truncate (metadata (.node 159 0))) publicCache) {}
  change WithinSigns LIFETIME _ at within
  exact run_returns _ _ (start_signed_card nonces metadata _ LIFETIME within budget) _ _ result member

attribute [local irreducible] SecurityMonitorGraphView.experiment

theorem experiment_marks (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) (result : Outcome (Result SecurityExperiment.Result))
    (member : result ∈ support (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)) :
    SecurityIndexTrace.marks result.value.history.indexTrace ≤ LIFETIME := by
  have history := experiment_history publicCache adversary rounds budget result member
  exact history.1.marks_lifetime history.2

end SigGolfCandidate.Hypertree.SecurityMonitorGraphLifetime
