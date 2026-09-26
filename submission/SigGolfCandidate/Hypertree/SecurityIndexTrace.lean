import SigGolfCandidate.Hypertree.SecurityGraphPassive
import VCVio.EvalDist.Expectation

/-! Inlined from SigGolfCandidate.Hypertree.SecurityIndexMonitor; its only importer was SigGolfCandidate.Hypertree.SecurityIndexTrace. -/
section
namespace SigGolfCandidate.Hypertree.SecurityIndexMonitor
open SigGolf OracleComp OracleSpec OracleComp.EvalDist
set_option backward.isDefEq.respectTransparency false

/-- A marked draw is a first signing index, chosen before its hash answer is known. -/
inductive Strategy where
  | done
  | draw (mark : Bool) (next : BitVec 256 → Strategy)
  | coin (n : Nat) (next : Fin (n+1) → Strategy)

/-- Expected number of fresh index-oracle calls, including signing draws. -/
noncomputable def cost : Strategy → ENNReal
  | .done => 0
  | .draw _ next => 1 + expectedValue ($ᵗ BitVec 256) (fun answer => cost (next answer))
  | .coin n next => expectedValue ($ᵗ Fin (n+1)) (fun answer => cost (next answer))

/-- The flag remains passive. Exhausting the marking allowance turns later draws into ordinary probes. -/
noncomputable def play : Strategy → Finset (BitVec 160) → Finset (BitVec 160) → Nat → ProbComp Bool
  | .done, _, _, _ => pure false
  | .coin n next, seen, marked, remaining => do
      let answer ← $ᵗ Fin (n+1)
      play (next answer) seen marked remaining
  | .draw mark next, seen, marked, remaining => do
      let answer ← $ᵗ BitVec 256
      let index := answer.extractLsb' 0 160
      if mark = true ∧ 0 < remaining then
        let later ← play (next answer) (insert index seen) (insert index marked) (remaining-1)
        pure (decide (index ∈ seen) || later)
      else
        let later ← play (next answer) (insert index seen) marked remaining
        pure (decide (index ∈ marked) || later)

theorem prob_bind_le {α : Type} (draw : ProbComp α) (next : α → ProbComp Bool)
    (bound : α → ENNReal) (upper : ∀ answer, Pr[fun hit => hit = true | next answer] ≤ bound answer) :
    Pr[fun hit => hit = true | draw >>= next] ≤ expectedValue draw bound := by
  rw [probEvent_bind_eq_tsum, expectedValue_def]
  exact ENNReal.tsum_le_tsum (fun answer => mul_le_mul' le_rfl (upper answer))

/-- One marked or unmarked draw, with the future potential bounded uniformly. -/
theorem draw_bound (targets : Finset (BitVec 160)) (next : BitVec 256 → ProbComp Bool)
    (work : BitVec 256 → ENNReal) (future initial limit : Nat)
    (upper : ∀ answer, Pr[fun hit => hit = true | next answer] ≤
      (future : ENNReal) / 2^160 + (limit : ENNReal) / 2^160 * work answer)
    (amortized : targets.card + future ≤ initial + limit) :
    Pr[fun hit => hit = true | (do
      let answer ← $ᵗ BitVec 256
      let later ← next answer
      pure (decide (answer.extractLsb' 0 160 ∈ targets) || later))] ≤
      (initial : ENNReal) / 2^160 + (limit : ENNReal) / 2^160 *
        (1 + expectedValue ($ᵗ BitVec 256) work) := by
  have first := SecurityGraphPassive.passive_or_le ($ᵗ BitVec 256)
    (fun answer => decide (answer.extractLsb' 0 160 ∈ targets)) next
  have density : Pr[fun answer : BitVec 256 => decide (answer.extractLsb' 0 160 ∈ targets) = true |
      $ᵗ BitVec 256] = (targets.card : ENNReal) / 2^160 := by
    simpa only [decide_eq_true_eq] using SecurityUniform.prob_extract_mem 96 160 targets
  rw [density] at first
  have rest := prob_bind_le ($ᵗ BitVec 256) next _ upper
  have integral : expectedValue ($ᵗ BitVec 256)
      (fun answer => (future : ENNReal)/2^160+(limit : ENNReal)/2^160*work answer) =
      (future : ENNReal)/2^160+(limit : ENNReal)/2^160*expectedValue ($ᵗ BitVec 256) work := by
    rw [expectedValue_add, expectedValue_const NeverFail.probFailure_eq_zero]
    simp only [mul_comm ((limit : ENNReal)/2^160), expectedValue_mul_const]
  rw [integral] at rest
  have arithmetic : ((targets.card : ENNReal)+(future : ENNReal))/2^160 ≤
      ((initial : ENNReal)+(limit : ENNReal))/2^160 := by
    apply ENNReal.div_le_div _ le_rfl
    exact_mod_cast amortized
  calc
    _ ≤ (targets.card : ENNReal)/2^160 + ((future : ENNReal)/2^160 +
      (limit : ENNReal)/2^160*expectedValue ($ᵗ BitVec 256) work) := first.trans (add_le_add le_rfl rest)
    _ = ((targets.card : ENNReal)+(future : ENNReal))/2^160 +
      (limit : ENNReal)/2^160*expectedValue ($ᵗ BitVec 256) work := by rw [ENNReal.add_div]; ac_rfl
    _ ≤ ((initial : ENNReal)+(limit : ENNReal))/2^160 +
      (limit : ENNReal)/2^160*expectedValue ($ᵗ BitVec 256) work := add_le_add arithmetic le_rfl
    _ = _ := by rw [ENNReal.add_div, mul_add, mul_one, add_assoc]

/-- Earlier probes are charged when a later signing draw collides with them. The
potential accounts for that deferred charge without assuming nonadaptive messages. -/
theorem prob_play_le (strategy : Strategy) (seen marked : Finset (BitVec 160)) (remaining limit : Nat)
    (allowance : marked.card + remaining ≤ limit) :
    Pr[fun hit => hit = true | play strategy seen marked remaining] ≤
      ((remaining * seen.card : Nat) : ENNReal)/2^160 + (limit : ENNReal)/2^160 * cost strategy := by
  induction strategy generalizing seen marked remaining with
  | done => simp [play, cost]
  | coin n next ih =>
    simp only [play, cost]
    have bound := prob_bind_le ($ᵗ Fin (n+1))
      (fun answer => play (next answer) seen marked remaining) _ (fun answer => ih answer seen marked remaining allowance)
    rw [expectedValue_add, expectedValue_const NeverFail.probFailure_eq_zero] at bound
    simpa only [mul_comm ((limit : ENNReal)/2^160), expectedValue_mul_const] using bound
  | draw mark next ih =>
    by_cases marking : mark = true ∧ 0 < remaining
    · simp only [play, if_pos marking, cost]
      apply draw_bound seen _ _ ((remaining-1)*(seen.card+1)) (remaining*seen.card) limit
      · intro answer
        have nextAllowance : (insert (answer.extractLsb' 0 160) marked).card + (remaining-1) ≤ limit := by
          have bound := Finset.card_insert_le (answer.extractLsb' 0 160) marked
          omega
        exact (ih answer _ _ _ nextAllowance).trans (add_le_add
          (ENNReal.div_le_div (by exact_mod_cast (Nat.mul_le_mul_left (remaining-1)
              (Finset.card_insert_le (answer.extractLsb' 0 160) seen))) le_rfl) le_rfl)
      · have positive := marking.2
        have identity : remaining = (remaining-1)+1 := by omega
        conv_rhs => rw [identity]
        simp only [Nat.add_mul, Nat.one_mul]
        rw [Nat.mul_add, Nat.mul_one]
        omega
    · simp only [play, if_neg marking, cost]
      apply draw_bound marked _ _ (remaining*(seen.card+1)) (remaining*seen.card) limit
      · intro answer
        exact (ih answer _ _ _ allowance).trans (add_le_add
          (ENNReal.div_le_div (by exact_mod_cast (Nat.mul_le_mul_left remaining
              (Finset.card_insert_le (answer.extractLsb' 0 160) seen))) le_rfl) le_rfl)
      · rw [Nat.mul_add, Nat.mul_one]
        omega

/-- At most L marked signing draws spend at most L/2^160 per expected fresh H5 call. -/
theorem prob_empty_le (strategy : Strategy) (limit : Nat) :
    Pr[fun hit => hit = true | play strategy ∅ ∅ limit] ≤ (limit : ENNReal)/2^160 * cost strategy := by
  simpa using prob_play_le strategy ∅ ∅ limit limit (by simp)

/-- Observable fresh-call counter under exactly the same answers seen by the strategy. -/
noncomputable def draws : Strategy → ProbComp Nat
  | .done => pure 0
  | .draw _ next => do
      let answer ← $ᵗ BitVec 256
      (fun count => count+1) <$> draws (next answer)
  | .coin n next => do
      let answer ← $ᵗ Fin (n+1)
      draws (next answer)

theorem cost_eq_expected (strategy : Strategy) :
    cost strategy = expectedValue (draws strategy) (fun count => (count : ENNReal)) := by
  induction strategy with
  | done => simp [cost, draws]
  | coin n next ih => simp only [cost, draws, expectedValue_bind, ih]
  | draw mark next ih =>
    simp only [cost, draws, expectedValue_bind, expectedValue_map, Nat.cast_add, Nat.cast_one,
      expectedValue_add, expectedValue_const NeverFail.probFailure_eq_zero, ih]
    exact add_comm _ _

theorem prob_lifetime_le (strategy : Strategy) :
    Pr[fun hit => hit = true | play strategy ∅ ∅ LIFETIME] ≤
      expectedValue (draws strategy) (fun count => (count : ENNReal)) / 2^128 := by
  have bound := prob_empty_le strategy LIFETIME
  rw [cost_eq_expected] at bound
  have rate : (LIFETIME : ENNReal)/2^160 = 1/(2:ENNReal)^128 := by
    apply (ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)).2
    norm_num [LIFETIME]
  simpa only [rate, div_eq_mul_inv, one_mul, mul_comm] using bound

/-- info: 'SigGolfCandidate.Hypertree.SecurityIndexMonitor.prob_lifetime_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prob_lifetime_le
end SigGolfCandidate.Hypertree.SecurityIndexMonitor

end

namespace SigGolfCandidate.Hypertree.SecurityIndexTrace
open SigGolf OracleComp OracleSpec SecurityIndexMonitor
set_option backward.isDefEq.respectTransparency false

abbrev Entry := Bool × BitVec 160

def marks : List Entry → Nat
  | [] => 0
  | entry :: tail => (if entry.1 then 1 else 0) + marks tail

/-- Every fresh H5 answer is retained, including probes before a first signing request. -/
noncomputable def trace : Strategy → ProbComp (List Entry)
  | .done => pure []
  | .draw mark next => do
      let answer ← $ᵗ BitVec 256
      (fun tail => (mark,answer.extractLsb' 0 160)::tail) <$> trace (next answer)
  | .coin n next => do
      let answer ← $ᵗ Fin (n+1)
      trace (next answer)

def replay : List Entry → Finset (BitVec 160) → Finset (BitVec 160) → Nat → Bool
  | [], _, _, _ => false
  | (mark,index)::tail, seen, marked, remaining =>
      if mark = true ∧ 0 < remaining then
        decide (index ∈ seen) || replay tail (insert index seen) (insert index marked) (remaining-1)
      else decide (index ∈ marked) || replay tail (insert index seen) marked remaining

theorem play_eq_trace (strategy : Strategy) (seen marked : Finset (BitVec 160)) (remaining : Nat) :
    play strategy seen marked remaining =
      (fun entries => replay entries seen marked remaining) <$> trace strategy := by
  induction strategy generalizing seen marked remaining with
  | done => simp [play, trace, replay]
  | coin n next ih => simp only [play, trace, map_bind, ih]
  | draw mark next ih =>
    simp only [play, trace, map_bind, Functor.map_map]
    apply bind_congr
    intro answer
    by_cases marking : mark = true ∧ 0 < remaining
    · simp [marking, ih, replay, Functor.map_map]
    · simp [marking, ih, replay, Functor.map_map]

/-- No repeated index involving a marked entry, including a later marked entry. -/
def Conflict : List Entry → Prop
  | [] => False
  | entry :: tail =>
      (∃ other ∈ tail, entry.2 = other.2 ∧ (entry.1 = true ∨ other.1 = true)) ∨ Conflict tail

def Safe : Finset (BitVec 160) → Finset (BitVec 160) → List Entry → Prop
  | _, _, [] => True
  | seen, marked, (mark,index)::tail =>
      index ∉ marked ∧ (mark = true → index ∉ seen) ∧
        Safe (insert index seen) (if mark then insert index marked else marked) tail

theorem replay_safe (entries : List Entry) (seen marked : Finset (BitVec 160)) (remaining : Nat)
    (included : marked ⊆ seen) (budget : marks entries ≤ remaining)
    (noHit : replay entries seen marked remaining = false) : Safe seen marked entries := by
  induction entries generalizing seen marked remaining with
  | nil => trivial
  | cons entry tail ih =>
    rcases entry with ⟨mark,index⟩
    cases mark with
    | false =>
      simp only [replay, Bool.false_eq_true, false_and, ↓reduceIte, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at noHit
      simp only [marks, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at budget
      exact ⟨noHit.1, by simp, ih _ _ remaining
        (fun point present => Finset.mem_insert_of_mem (included present)) budget noHit.2⟩
    | true =>
      have positive : 0 < remaining := by simp only [marks, ↓reduceIte] at budget; omega
      simp only [replay, positive, and_self, ↓reduceIte, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at noHit
      have tailBudget : marks tail ≤ remaining-1 := by simp only [marks, ↓reduceIte] at budget; omega
      exact ⟨fun present => noHit.1 (included present), fun _ => noHit.1,
        ih _ _ (remaining-1) (Finset.insert_subset_insert _ included) tailBudget noHit.2⟩

theorem safe_marked_excludes (entries : List Entry) (seen marked : Finset (BitVec 160))
    (safe : Safe seen marked entries) (index : BitVec 160) (known : index ∈ marked) :
    ∀ entry ∈ entries, entry.2 ≠ index := by
  induction entries generalizing seen marked with
  | nil => simp
  | cons entry tail ih =>
    rcases entry with ⟨mark,value⟩
    intro other member
    rcases List.mem_cons.mp member with same | later
    · subst other
      intro same
      exact safe.1 (by change value = index at same; exact same.symm ▸ known)
    · apply ih _ _ safe.2.2 ?_ other later
      cases mark <;> simp_all

theorem safe_seen_excludes (entries : List Entry) (seen marked : Finset (BitVec 160))
    (safe : Safe seen marked entries) (index : BitVec 160) (known : index ∈ seen) :
    ∀ entry ∈ entries, entry.1 = true → entry.2 ≠ index := by
  induction entries generalizing seen marked with
  | nil => simp
  | cons entry tail ih =>
    rcases entry with ⟨mark,value⟩
    intro other member markedEntry
    rcases List.mem_cons.mp member with same | later
    · subst other
      intro same
      exact safe.2.1 markedEntry (by change value = index at same; exact same.symm ▸ known)
    · exact ih _ _ safe.2.2 (Finset.mem_insert_of_mem known) other later markedEntry

theorem safe_no_conflict (entries : List Entry) (seen marked : Finset (BitVec 160))
    (safe : Safe seen marked entries) : ¬Conflict entries := by
  induction entries generalizing seen marked with
  | nil => simp [Conflict]
  | cons entry tail ih =>
    rcases entry with ⟨mark,index⟩
    intro conflict
    rcases conflict with ⟨other,member,same,first | second⟩ | later
    · have known : index ∈ (if mark then insert index marked else marked) := by cases mark <;> simp_all
      exact safe_marked_excludes tail _ _ safe.2.2 index known other member same.symm
    · exact safe_seen_excludes tail _ _ safe.2.2 index (Finset.mem_insert_self _ _) other member second same.symm
    · exact ih _ _ safe.2.2 later

theorem conflict_detected (entries : List Entry) (limit : Nat) (budget : marks entries ≤ limit)
    (conflict : Conflict entries) : replay entries ∅ ∅ limit = true := by
  cases hit : replay entries ∅ ∅ limit with
  | true => rfl
  | false => exact False.elim (safe_no_conflict entries ∅ ∅
      (replay_safe entries ∅ ∅ limit (by simp) budget hit) conflict)

theorem trace_length (strategy : Strategy) : List.length <$> trace strategy = draws strategy := by
  induction strategy with
  | done => rfl
  | coin n next ih => simp only [trace, draws, map_bind, ih]
  | draw mark next ih =>
    simp only [trace, draws, map_bind, Functor.map_map]
    apply bind_congr
    intro answer
    rw [← ih answer, Functor.map_map]
    rfl

/-- Every actual index collision involving a signing draw is covered, whether
that signing draw came before or after the other query. -/
theorem prob_conflict_le (strategy : Strategy) (limit : Nat) :
    Pr[fun entries => Conflict entries ∧ marks entries ≤ limit | trace strategy] ≤
      (limit : ENNReal)/2^160 * cost strategy := by
  have bound := prob_empty_le strategy limit
  rw [play_eq_trace, probEvent_map] at bound
  apply le_trans _ bound
  apply probEvent_mono
  intro entries _ bad
  exact conflict_detected entries limit bad.2 bad.1

theorem conflict_of_pair (before between after : List Entry) (first second : Entry)
    (same : first.2 = second.2) (marked : first.1 = true ∨ second.1 = true) :
    Conflict (before ++ first :: (between ++ second :: after)) := by
  induction before with
  | nil => exact Or.inl ⟨second, List.mem_append_right _ (List.mem_cons_self ..), same, marked⟩
  | cons entry before ih => exact Or.inr ih

theorem prob_lifetime_conflict_le (strategy : Strategy) :
    Pr[fun entries => Conflict entries ∧ marks entries ≤ LIFETIME | trace strategy] ≤
      OracleComp.EvalDist.expectedValue (trace strategy) (fun entries => (entries.length : ENNReal)) / 2^128 := by
  have bound := prob_lifetime_le strategy
  rw [play_eq_trace, probEvent_map, ← trace_length, OracleComp.EvalDist.expectedValue_map] at bound
  apply le_trans _ bound
  apply probEvent_mono
  intro entries _ bad
  exact conflict_detected entries LIFETIME bad.2 bad.1

/-- info: 'SigGolfCandidate.Hypertree.SecurityIndexTrace.prob_lifetime_conflict_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prob_lifetime_conflict_le
end SigGolfCandidate.Hypertree.SecurityIndexTrace
