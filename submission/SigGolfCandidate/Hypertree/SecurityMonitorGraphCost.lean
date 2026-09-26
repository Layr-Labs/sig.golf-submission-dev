import SigGolfCandidate.Hypertree.SecurityGraphMonitorReturns
import SigGolfCandidate.Hypertree.SecurityMonitorGraphView

/-! Inlined from SigGolfCandidate.Hypertree.SecurityGraphMonitorCredit; its only importer was SigGolfCandidate.Hypertree.SecurityMonitorGraphCost. -/
section
namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier SecurityGraphPassive
  SecurityDerivation SecurityGraph SecurityGraphQuery SecurityGraphChainMonitor SecurityGraphFactor
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A pathwise test ledger: `spent` plus all remaining passive tests is bounded
by the allowance read from the final public result. This retains adaptive costs. -/
def Credit {α : Type} (allowance : α → Nat) : Nat → Program α → Prop
  | spent, .done value => spent ≤ allowance value
  | spent, .reveal _ next => ∀ answer, Credit allowance spent (next answer)
  | spent, .guess _ _ next => Credit allowance (spent + 1) next
  | spent, .coin _ next => ∀ answer, Credit allowance spent (next answer)
  | spent, .bits next => ∀ answer, Credit allowance spent (next answer)
  | spent, .collision _ next => ∀ answer, Credit allowance (spent + 1) (next answer)

theorem Credit.weaken {α : Type} (allowance : α → Nat) (program : Program α)
    {first second : Nat} (less : first ≤ second) (credit : Credit allowance second program) :
    Credit allowance first program := by
  induction program generalizing first second with
  | done value => exact less.trans credit
  | guess point value next ih => exact ih (Nat.add_le_add_right less 1) credit
  | reveal point next ih | coin n next ih | bits next ih =>
    exact fun answer => ih answer less (credit answer)
  | collision target next ih => exact fun answer => ih answer (Nat.add_le_add_right less 1) (credit answer)

/-- The ledger bounds the actual sampled test counter on every supported path,
even after a bad event, since no branch can inspect the passive flag. -/
theorem run_credit {α : Type} (allowance : α → Nat) (program : Program α) (spent : Nat)
    (credit : Credit allowance spent program) (table : PointTable) (cache : QueryCache PointSpec)
    (result : Outcome α) (member : result ∈ support (run table cache program)) :
    spent + result.tests ≤ allowance result.value := by
  induction program generalizing spent cache result with
  | done value =>
    simp only [run, support_pure, Set.mem_singleton_iff] at member
    subst result
    simpa only [Nat.add_zero, Credit] using credit
  | reveal point next ih => exact ih (table point) spent (credit _) _ _ member
  | guess point value next ih =>
    simp only [run, support_map, Set.mem_image] at member
    obtain ⟨earlier, supported, same⟩ := member
    subst result
    have bound := ih (spent + 1) credit cache earlier supported
    change spent + (earlier.tests + 1) ≤ allowance earlier.value
    omega
  | coin n next ih | bits next ih =>
    rw [run, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    exact ih answer spent (credit _) cache result member
  | collision target next ih =>
    simp only [run, mem_support_bind_iff, support_map, Set.mem_image] at member
    obtain ⟨answer, _, earlier, supported, same⟩ := member
    subst result
    have bound := ih answer (spent + 1) (credit answer) cache earlier supported
    change spent + (earlier.tests + 1) ≤ allowance earlier.value
    omega

theorem disclose_credit {α : Type} (allowance : α → Nat) (spent : Nat) (points : List Point)
    (cache : QueryCache PointSpec) (next : QueryCache PointSpec → Program α)
    (credit : ∀ opened, Credit allowance spent (next opened)) :
    Credit allowance spent (SecurityGraphMonitorOracle.disclose points cache next) := by
  induction points generalizing cache with
  | nil => exact credit cache
  | cons point rest ih => exact fun answer => ih (cache.cacheQuery point answer)

theorem residualStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 1) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.residualStep exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.residualStep
  cases cache query with
  | some answer => exact Credit.weaken allowance _ (by omega) (credit answer exposed cache)
  | none =>
    cases exposed target with
    | some value => exact fun answer => credit answer exposed _
    | none => exact fun answer => credit answer exposed _

theorem chainStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7)
    (query : Query) (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 2) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) := by
  have residual := residualStep_credit allowance (spent + 1) exposed cache query (successor address step) next credit
  unfold SecurityGraphMonitorOracle.chainStep
  cases payload address step query with
  | none => exact Credit.weaken allowance _ (by omega) residual
  | some point =>
    cases exposed (predecessor address step) with
    | none => exact residual
    | some value =>
      dsimp only
      split
      · exact fun answer => Credit.weaken allowance _ (by omega) (credit answer _ _)
      · exact Credit.weaken allowance _ (by omega) residual

theorem knownResidual_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query) (target : Option Digest)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 1) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.knownResidual exposed cache query target next) := by
  unfold SecurityGraphMonitorOracle.knownResidual
  cases cache query with
  | some answer => exact Credit.weaken allowance _ (by omega) (credit answer exposed cache)
  | none =>
    cases target with
    | some value => exact fun answer => credit answer exposed _
    | none => exact fun answer => Credit.weaken allowance _ (by omega) (credit answer exposed _)

/-- At most two test credits are consumed by each graph-address query. -/
theorem publicStep_credit {α : Type} (allowance : α → Nat) (spent : Nat) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance (spent + 2) (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  have known exposed := knownResidual_credit allowance (spent + 1) exposed cache query
  unfold SecurityGraphMonitorOracle.publicStep
  cases locate query with
  | none => exact Credit.weaken allowance _ (by omega) (known exposed none next credit)
  | some position =>
    cases position with
    | chain address step => exact chainStep_credit allowance spent exposed cache address step query next credit
    | leaf level tree side | node level tree =>
      apply disclose_credit
      intro opened
      dsimp only
      split
      · exact Credit.weaken allowance _ (by omega) (credit _ _ _)
      · exact Credit.weaken allowance _ (by omega) (known opened _ next credit)

/-- Queries outside graph addresses consume no graph-test credits at all. -/
theorem publicStep_outside_credit {α : Type} (allowance : α → Nat) (spent : Nat) (metadata : MetadataTable)
    (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (outside : locate query = none)
    (credit : ∀ answer opened residual, Credit allowance spent (next answer opened residual)) :
    Credit allowance spent (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  simp only [SecurityGraphMonitorOracle.publicStep, outside, SecurityGraphMonitorOracle.knownResidual]
  cases cache query with
  | some answer => exact credit answer exposed cache
  | none => exact fun answer => credit answer exposed _

end SigGolfCandidate.Hypertree.SecurityGraphMonitorProgram

end

namespace SigGolfCandidate.Hypertree.SecurityMonitorGraphCost
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFactor SecurityGraphPassive SecurityGraphMonitorProgram SecurityGraphMonitorSign
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityIndexQuery
  SecuritySeparation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

theorem located_not_secretKey (query : Query) (position : Position) (located : locate query = some position) :
    ¬SecretKeyEligible query := by
  unfold locate at located
  split at located
  next found =>
    obtain ⟨payload, equal⟩ := found.choose_spec
    rw [← equal]
    cases found.choose with
    | chain address step => exact SecurityDomains.not_secretKeyEligible_addressedInput 2 _ _ _ _ _ _ (by decide) (by decide)
    | leaf level tree side => exact SecurityDomains.not_secretKeyEligible_addressedInput 3 _ _ _ _ _ _ (by decide) (by decide)
    | node level tree => exact SecurityDomains.not_secretKeyEligible_addressedInput 4 _ _ _ _ _ _ (by decide) (by decide)
  next absent => cases located

theorem parsed_graph_mono (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKeyEligible cached : Bool) (answer : BitVec 256) :
    history.counts.graph ≤ (recordParsed history query parsed secretKeyEligible cached answer).counts.graph := by
  cases parsed with
  | some pair => exact Nat.le_refl _
  | none =>
    cases secretKeyEligible <;> simp only [recordParsed, Bool.false_eq_true, if_false, if_true] <;> omega

attribute [local irreducible] recordParsed

theorem public_graph_mono (history : History) (query : Query) (cached : Bool) (answer : BitVec 256) :
    history.counts.graph ≤ (recordPublic history query cached answer).counts.graph :=
  parsed_graph_mono history query (parse query) (decide (SecretKeyEligible query)) cached answer

theorem public_graph_located (history : History) (query : Query) (cached : Bool)
    (answer : BitVec 256) (position : Position) (located : locate query = some position) :
    (recordPublic history query cached answer).counts.graph = history.counts.graph + 1 := by
  have unparsed : parse query = none := by
    cases parsed : parse query with
    | none => rfl
    | some pair =>
      have serialized := (parse_some_iff query pair).mp parsed
      have outside := locate_index pair.1 pair.2
      rw [serialized, located] at outside
      cases outside
  change (recordParsed history query (parse query) (decide (SecretKeyEligible query)) cached answer).counts.graph = _
  rw [unparsed]
  simp only [decide_eq_false (located_not_secretKey query position located), recordParsed, Bool.false_eq_true, if_false]

/-- The shared query classifier spends graph credits only on its own class.
Secret key and parsed-index queries pass through with zero graph-contact tests. -/
theorem public_record_credit {α : Type} (allowance : α → Nat) (history : History)
    (metadata : MetadataTable) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened residual, Credit allowance
      (2 * (recordPublic history query (cache query).isSome answer).counts.graph) (next answer opened residual)) :
    Credit allowance (2 * history.counts.graph)
      (SecurityGraphMonitorOracle.publicStep metadata exposed cache query next) := by
  cases located : locate query with
  | none =>
    apply publicStep_outside_credit _ _ _ _ _ _ _ located
    intro answer opened residual
    exact Credit.weaken allowance _ (Nat.mul_le_mul_left 2 (public_graph_mono history query _ answer))
      (credit answer opened residual)
  | some position =>
    apply publicStep_credit
    intro answer opened residual
    have nextCredit := credit answer opened residual
    rw [public_graph_located history query _ answer position located] at nextCredit
    convert nextCredit using 1 <;> omega

theorem indexStep_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (cache : QueryCache HashSpec) (query : Query) (next : BitVec 256 → QueryCache HashSpec → Program α)
    (credit : ∀ answer residual, Credit allowance spent (next answer residual)) :
    Credit allowance spent (indexStep cache query next) := by
  unfold indexStep
  cases cache query with
  | some answer => exact credit answer cache
  | none => exact fun answer => credit answer _

/-- Actual graph tests are charged to graph-class calls in the same adaptive
execution, preserving the secret key and index portions of the shared budget. -/
theorem compile_credit {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (remaining : Nat) (exposed : QueryCache PointSpec) (cache : QueryCache HashSpec)
    (history : History) :
    Credit (fun result : Result α => 2 * result.history.counts.graph) (2 * history.counts.graph)
      (compile nonces metadata view remaining exposed cache history) := by
  induction view generalizing remaining exposed cache history with
  | done value => exact Nat.le_refl _
  | coin n next ih => exact fun answer => ih answer remaining exposed cache history
  | hash query next ih =>
    cases remaining with
    | zero => exact Nat.le_refl _
    | succ remaining =>
      apply public_record_credit
      intro answer opened residual
      exact ih answer remaining opened residual _
  | sign message next ih =>
    unfold compile
    split
    next enough =>
      apply indexStep_credit
      intro answer residual
      apply disclose_credit
      intro opened
      apply Credit.weaken _ _ _ (ih _ (remaining - 117508) opened residual
        (recordSign history message (cache (SecurityRandomOracle.indexInput message (nonces message))).isSome answer))
      change 2 * history.counts.graph ≤ 2 * (history.counts.graph + 117507)
      omega
    next short => exact Nat.le_refl _

theorem start_credit {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) :
    Credit (fun result : Result α => 2 * result.history.counts.graph) 0
      (start nonces metadata view budget) := by
  unfold start
  split
  next enough =>
    apply disclose_credit
    intro exposed
    exact Credit.weaken _ _ (Nat.zero_le _)
      (compile_credit nonces metadata view (budget - 739) exposed ∅ (recordKeygen {}))
  next short => exact Nat.zero_le _

/-- Pathwise graph-counter domination in the actual common passive execution. -/
theorem start_tests_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) (result : Outcome (Result α))
    (member : result ∈ support (SecurityGraphMonitorProgram.experiment (start nonces metadata view budget) ∅)) :
    result.tests ≤ 2 * result.value.history.counts.graph := by
  rw [SecurityGraphMonitorProgram.experiment, mem_support_bind_iff] at member
  obtain ⟨table, _, member⟩ := member
  simpa only [Nat.zero_add] using run_credit _ _ 0 (start_credit nonces metadata view budget) _ _ result member

/-- Graph-contact probability uses only graph-class charged calls in this same
simulation. The nonce/index and secret key classes retain their own budget shares. -/
theorem start_bad_le {α : Type} (nonces : NonceTable) (metadata : MetadataTable)
    (view : View α) (budget : Nat) :
    Pr[fun result => result.bad = true |
      SecurityGraphMonitorProgram.experiment (start nonces metadata view budget) ∅] ≤
      2 * expectedValue (SecurityGraphMonitorProgram.experiment (start nonces metadata view budget) ∅)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128 := by
  apply (prob_bad_le_expected (start nonces metadata view budget) ∅).trans
  apply ENNReal.div_le_div _ le_rfl
  calc
    _ ≤ expectedValue (SecurityGraphMonitorProgram.experiment (start nonces metadata view budget) ∅)
        (fun result => 2 * (result.value.history.counts.graph : ENNReal)) := by
      apply expectedValue_mono_of_support
      intro result member
      exact_mod_cast start_tests_le nonces metadata view budget result member
    _ = _ := by simp only [mul_comm (2 : ENNReal), expectedValue_mul_const]

/-- The fully concrete adversary experiment inherits the graph bound with its
own expected graph-class count; there is no cost transfer across a bad event. -/
theorem experiment_bad_le (publicCache : Cache) (adversary : Adversary submission.sizes)
    (rounds budget : Nat) :
    Pr[fun result => result.bad = true | SecurityMonitorGraphView.experiment publicCache adversary rounds budget] ≤
      2 * expectedValue (SecurityMonitorGraphView.experiment publicCache adversary rounds budget)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128 := by
  unfold SecurityMonitorGraphView.experiment
  simp only [probEvent_bind_eq_expectedValue, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ NonceTable) (fun nonces => expectedValue ($ᵗ MetadataTable) (fun metadata =>
      2 * expectedValue (SecurityGraphMonitorProgram.experiment
        (start nonces metadata
          (ofInteract adversary (truncate (metadata (.node 159 0))) rounds
            (adversary.initial (truncate (metadata (.node 159 0))) publicCache) {}) budget) ∅)
        (fun result => (result.value.history.counts.graph : ENNReal)) / 2 ^ 128)) := by
      apply expectedValue_mono
      intro nonces
      apply expectedValue_mono
      intro metadata
      exact start_bad_le nonces metadata _ budget
    _ = _ := by
      simp only [div_eq_mul_inv, mul_comm (2 : ENNReal), expectedValue_mul_const]

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorGraphCost.experiment_bad_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms experiment_bad_le

end SigGolfCandidate.Hypertree.SecurityMonitorGraphCost
