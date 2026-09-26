import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorOracle67

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCredit67
open SigGolf OracleComp OracleSpec Reference
  GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67 GroupedBalancedGraphMonitorProgram67
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

theorem disclose_credit {α : Type} (allowance : α → Nat) (spent : Nat)
    (points : List Point) (exposed : QueryCache PointSpec)
    (next : QueryCache PointSpec → Program α)
    (credit : ∀ opened, Credit allowance spent (next opened)) :
    Credit allowance spent
      (GroupedBalancedGraphMonitorOracle67.disclose points exposed next) := by
  induction points generalizing exposed with
  | nil => exact credit exposed
  | cons point rest ih => exact fun answer => ih _

theorem residualStep_credit {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance (spent + 1) (next answer opened cache)) :
    Credit allowance spent
      (GroupedBalancedGraphMonitorOracle67.residualStep exposed residual query target next) := by
  unfold GroupedBalancedGraphMonitorOracle67.residualStep
  cases residual query with
  | some answer => exact Credit.weaken allowance _ (by omega) (credit answer exposed residual)
  | none =>
      cases exposed target with
      | some value => exact fun answer => credit answer exposed _
      | none => exact fun answer => credit answer exposed _

theorem chainStep_credit {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (position : Position) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance (spent + 2) (next answer opened cache)) :
    Credit allowance spent
      (GroupedBalancedGraphMonitorOracle67.chainStep exposed residual position query next) := by
  have residualCredit := residualStep_credit allowance (spent + 1) exposed
    residual query (.inl position) next credit
  unfold GroupedBalancedGraphMonitorOracle67.chainStep
  cases predEq : GroupedBalancedGraphMonitorPredecessor67.predecessor position.val with
  | none =>
      by_cases canonical : query = position.input []
      · simp only [if_pos canonical]
        exact fun answer => Credit.weaken allowance _
          (show spent ≤ spent + 2 by omega) (credit answer _ _)
      · simp only [if_neg canonical]
        exact Credit.weaken allowance _
          (show spent ≤ spent + 1 by omega) residualCredit
  | some predPoint =>
      dsimp
      cases parsed : GroupedBalancedGraphMonitorOracle67.parsedChainPayload position query with
      | none =>
          change Credit allowance spent
            (GroupedBalancedGraphMonitorOracle67.residualStep exposed residual query
              (.inl position) next)
          exact Credit.weaken allowance _
            (show spent ≤ spent + 1 by omega) residualCredit
      | some point =>
          dsimp
          cases knownEq : exposed predPoint with
          | none =>
              dsimp
              change Credit allowance (spent + 1)
                (GroupedBalancedGraphMonitorOracle67.residualStep exposed residual query
                  (.inl position) next)
              exact residualCredit
          | some knownValue =>
              dsimp
              by_cases canonical : point = truncate knownValue
              · simp only [if_pos canonical]
                change ∀ answer, Credit allowance spent
                  (next answer (exposed.cacheQuery (.inl position) answer) residual)
                exact fun answer => Credit.weaken allowance _
                  (show spent ≤ spent + 2 by omega) (credit answer _ _)
              · simp only [if_neg canonical]
                change Credit allowance spent
                  (GroupedBalancedGraphMonitorOracle67.residualStep exposed residual query
                    (.inl position) next)
                exact Credit.weaken allowance _
                  (show spent ≤ spent + 1 by omega) residualCredit

theorem publicStep_credit {α : Type} (allowance : α → Nat)
    (spent : Nat) (exposed : QueryCache PointSpec)
    (residual : QueryCache HashSpec) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (credit : ∀ answer opened cache,
      Credit allowance (spent + 2) (next answer opened cache)) :
    Credit allowance spent
      (GroupedBalancedGraphMonitorOracle67.publicStep exposed residual query next) := by
  unfold GroupedBalancedGraphMonitorOracle67.publicStep
  cases located : GroupedBalancedGraphQuery67.locate query with
  | none =>
      simp only [located]
      cases cached : residual query with
      | some answer =>
          simp only [cached]
          exact Credit.weaken allowance _
            (show spent ≤ spent + 2 by omega) (credit answer exposed residual)
      | none =>
          simp only [cached]
          exact fun answer => Credit.weaken allowance _
            (show spent ≤ spent + 2 by omega) (credit answer exposed _)
  | some position =>
      simp only [located]
      by_cases tagTwo : position.val.tag.val = 2
      · simp only [if_pos tagTwo]
        exact chainStep_credit allowance spent exposed residual position query next credit
      · simp only [if_neg tagTwo]
        apply disclose_credit
        intro opened
        split
        · exact fun answer => Credit.weaken allowance _
            (show spent ≤ spent + 2 by omega) (credit answer _ _)
        · exact Credit.weaken allowance _
            (show spent ≤ spent + 1 by omega)
            (residualStep_credit allowance (spent + 1) opened residual query
              (.inl position) next credit)


end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCredit67
