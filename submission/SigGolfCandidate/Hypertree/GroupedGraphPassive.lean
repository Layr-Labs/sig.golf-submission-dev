import SigGolfCandidate.Hypertree.GroupedGraphPayload
import Mathlib.Data.List.Sort
import SigGolfCandidate.Hypertree.SecurityGraphPassive
import SigGolfCandidate.Hypertree.GroupedGlobalPaired

/-! Inlined from SigGolfCandidate.Hypertree.GroupedGraphOrder; its only importer was SigGolfCandidate.Hypertree.GroupedGraphPassive. -/
section
/-! A small topological rank for the grouped public oracle graph. Bottom
leaves and paired chain starts have rank zero. All canonical dependencies
strictly precede the query that consumes them, and every rank is at most ten.
-/

namespace SigGolfCandidate.Hypertree.GroupedGraphOrder
open SigGolf GroupedSecurityGraph GroupedGraphPayload

private def addressCoordinates (address : SecurityGraph.Address) :
    Fin 256 × Fin 256 × BitVec 192 × Fin 256 × Fin 256 × Fin 256 :=
  (address.tag, address.level, address.tree,
    address.leaf, address.chain, address.step)

private theorem addressCoordinates_injective : Function.Injective addressCoordinates := by
  intro first second same
  cases first
  cases second
  simp only [addressCoordinates, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

instance : Finite SecurityGraph.Address :=
  Finite.of_injective addressCoordinates addressCoordinates_injective

instance : Finite Position := Finite.of_injective Subtype.val Subtype.val_injective
noncomputable instance : Fintype Position := Fintype.ofFinite Position

theorem groupBase_bounds (level : Nat) (low : 10 ≤ level) (high : level < 160) :
    groupBase level ≤ level ∧ level < groupBase level + 4 := by
  by_cases below : level < 148
  · have remainder := Nat.mod_add_div (level - 10) 3
    have small := Nat.mod_lt (level - 10) (by decide : 0 < 3)
    simp only [groupBase, if_pos below]
    omega
  · have remainder := Nat.mod_add_div (level - 148) 4
    have small := Nat.mod_lt (level - 148) (by decide : 0 < 4)
    simp only [groupBase, if_neg below]
    omega

theorem groupBase_previous (level : Nat) (low : 10 < level) (high : level < 160)
    (notBase : groupBase level ≠ level) :
    groupBase (level - 1) = groupBase level := by
  by_cases below : level < 148
  · have previousBelow : level - 1 < 148 := by omega
    have remainder := Nat.mod_add_div (level - 10) 3
    have previousRemainder := Nat.mod_add_div (level - 1 - 10) 3
    have small := Nat.mod_lt (level - 10) (by decide : 0 < 3)
    have previousSmall := Nat.mod_lt (level - 1 - 10) (by decide : 0 < 3)
    simp only [groupBase, if_pos below] at notBase
    simp only [groupBase, if_pos previousBelow, if_pos below]
    omega
  · have strict : 148 < level := by
      by_contra notStrict
      have same : level = 148 := by omega
      subst level
      exact notBase (by decide)
    have previousHigh : ¬ level - 1 < 148 := by omega
    have remainder := Nat.mod_add_div (level - 148) 4
    have previousRemainder := Nat.mod_add_div (level - 1 - 148) 4
    have small := Nat.mod_lt (level - 148) (by decide : 0 < 4)
    have previousSmall := Nat.mod_lt (level - 1 - 148) (by decide : 0 < 4)
    simp only [groupBase, if_neg below] at notBase
    simp only [groupBase, if_neg previousHigh, if_neg below]
    omega

def rank (position : Position) : Nat :=
  let address := position.val
  if address.tag.val = 2 then min address.step.val 4
  else if address.tag.val = 3 then 5
  else if address.level.val < 10 then address.level.val + 1
  else if address.level.val < 160 then
    6 + address.level.val - groupBase address.level.val
  else 0

theorem rank_le_ten (position : Position) : rank position ≤ 10 := by
  simp only [rank]
  split_ifs with htagTwo htagThree hlevelLow hlevelHigh
  · omega
  · omega
  · omega
  · have bound := groupBase_bounds position.val.level.val (by omega) hlevelHigh
    omega
  · omega

theorem bottom_leaf_rank (index : BitVec 160) : rank (bottomLeaf index) = 0 := by
  simp [rank, bottomLeaf]

theorem bottom_node_rank (level : Fin 10) (tree : BitVec 160) :
    rank (bottomNode level tree) = level.val + 1 := by
  have := level.isLt
  simp [rank, bottomNode, show level.val < 10 by omega]

theorem upper_chain_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) (step : Fin 5) :
    rank (upperChain base leaf chain step) = step.val := by
  have := step.isLt
  simp [rank, upperChain]
  omega

theorem upper_leaf_rank (base : Fin 150) (leaf : BitVec 160) :
    rank (upperLeaf base leaf) = 5 := by
  simp [rank, upperLeaf]

theorem upper_node_rank (level : Fin 150) (tree : BitVec 160) :
    rank (upperNode level tree) =
      6 + (level.val + 10) - groupBase (level.val + 10) := by
  have high : level.val + 10 < 160 := by have := level.isLt; omega
  have low : ¬level.val + 10 < 10 := by omega
  simp [rank, upperNode, high, low]

theorem bottom_node_child_rank (level : Fin 10) (tree : BitVec 160) :
    rank (nodeChildren (bottomNode level tree).val).1 <
      rank (bottomNode level tree) ∧
    rank (nodeChildren (bottomNode level tree).val).2 <
      rank (bottomNode level tree) := by
  by_cases zero : level.val = 0
  · have same : level = 0 := Fin.ext zero
    subst level
    rw [bottom_node_zero_children]
    simp [bottom_leaf_rank, bottom_node_rank]
  · let previous : Fin 9 := ⟨level.val - 1, by have := level.isLt; omega⟩
    have same : (⟨previous.val + 1, by omega⟩ : Fin 10) = level := by
      apply Fin.ext
      dsimp [previous]
      omega
    conv_lhs => rw [← same]
    conv_rhs => rw [← same]
    rw [bottom_node_step_children]
    simp only [bottom_node_rank]
    dsimp [previous]
    omega

theorem upper_chain_previous_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) (step : Fin 4) :
    rank (upperChain base leaf chain ⟨step.val, by omega⟩) <
      rank (upperChain base leaf chain ⟨step.val + 1, by omega⟩) := by
  rw [upper_chain_rank, upper_chain_rank]
  change step.val < step.val + 1
  omega

theorem upper_leaf_chain_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) :
    rank (upperChain base leaf chain ⟨4, by decide⟩) <
      rank (upperLeaf base leaf) := by
  rw [upper_chain_rank, upper_leaf_rank]
  decide

theorem upper_node_at_base_child_rank (level : Fin 150) (tree : BitVec 160)
    (atBase : groupBase (level.val + 10) = level.val + 10) :
    rank (nodeChildren (upperNode level tree).val).1 <
      rank (upperNode level tree) ∧
    rank (nodeChildren (upperNode level tree).val).2 <
      rank (upperNode level tree) := by
  rw [upper_node_at_base_children level tree atBase]
  simp only [upper_leaf_rank, upper_node_rank]
  rw [atBase]
  omega

theorem upper_node_inner_child_rank (level : Fin 150) (tree : BitVec 160)
    (positive : 0 < level.val)
    (notBase : groupBase (level.val + 10) ≠ level.val + 10) :
    rank (nodeChildren (upperNode level tree).val).1 <
      rank (upperNode level tree) ∧
    rank (nodeChildren (upperNode level tree).val).2 <
      rank (upperNode level tree) := by
  have high : level.val + 10 < 160 := by have := level.isLt; omega
  have sameBase := groupBase_previous (level.val + 10) (by omega) high notBase
  rw [upper_node_inner_children level tree positive notBase]
  simp only [upper_node_rank]
  change
    6 + (level.val - 1 + 10) - groupBase (level.val - 1 + 10) <
      6 + (level.val + 10) - groupBase (level.val + 10) ∧
    6 + (level.val - 1 + 10) - groupBase (level.val - 1 + 10) <
      6 + (level.val + 10) - groupBase (level.val + 10)
  have previousArgument : level.val - 1 + 10 = level.val + 10 - 1 := by omega
  rw [previousArgument, sameBase]
  have bound := groupBase_bounds (level.val + 10) (by omega) high
  omega

theorem rank_tag_four (position : Position)
    (tagFour : position.val.tag.val = 4) :
    rank position =
      if position.val.level.val < 10 then position.val.level.val + 1
      else if position.val.level.val < 160 then
        6 + position.val.level.val - groupBase position.val.level.val
      else 0 := by
  have notTwo : position.val.tag.val ≠ 2 := by omega
  have notThree : position.val.tag.val ≠ 3 := by omega
  simp only [rank, notTwo, notThree, ↓reduceIte]

theorem node_children_rank (position : Position)
    (tagFour : position.val.tag.val = 4)
    (small : position.val.level.val < 160) :
    rank (nodeChildren position.val).1 < rank position ∧
    rank (nodeChildren position.val).2 < rank position := by
  have tagged : rank position =
      if position.val.level.val < 10 then position.val.level.val + 1
      else 6 + position.val.level.val - groupBase position.val.level.val := by
    rw [rank_tag_four position tagFour]
    simp [small]
  by_cases lower : position.val.level.val < 10
  · by_cases zero : position.val.level.val = 0
    ·
      simp only [nodeChildren, dif_pos lower, dif_pos zero, Prod.fst, Prod.snd]
      rw [tagged]
      simp [lower, zero, bottom_leaf_rank]
    · let previous : Fin 10 := ⟨position.val.level.val - 1, by omega⟩
      simp only [nodeChildren, dif_pos lower, dif_neg zero, Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_pos lower, bottom_node_rank]
      omega
  · have upper : position.val.level.val < 160 := small
    by_cases atBase : position.val.level.val = groupBase position.val.level.val
    ·
      simp only [nodeChildren, dif_neg lower, dif_pos upper, dif_pos atBase,
        Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_neg lower, upper_leaf_rank]
      omega
    · have positive : 10 < position.val.level.val := by
        have bound := groupBase_bounds position.val.level.val (by omega) small
        by_contra notPositive
        have levelTen : position.val.level.val = 10 := by omega
        exact atBase (by simpa [levelTen, groupBase])
      have basePrev := groupBase_previous position.val.level.val positive small
        (Ne.symm atBase)
      simp only [nodeChildren, dif_neg lower, dif_pos upper, dif_neg atBase,
        Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_neg lower, upper_node_rank]
      have previousBound : position.val.level.val - 11 < 150 := by omega
      have previousLevel :
          (Fin.ofNat 150 (position.val.level.val - 11)).val + 10 =
            position.val.level.val - 1 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt previousBound]
        omega
      rw [previousLevel]
      rw [basePrev]
      have bound := groupBase_bounds position.val.level.val (by omega) small
      omega

/-- Symbolic complete graph order. The enormous address space is never
enumerated by the kernel; the sort and coverage proofs use finite-type laws. -/
noncomputable def positions : List Position :=
  (Finset.univ : Finset Position).toList.mergeSort
    (fun first second => decide (rank first ≤ rank second))

theorem positions_perm : positions.Perm (Finset.univ : Finset Position).toList :=
  List.mergeSort_perm _ _

theorem positions_nodup : positions.Nodup :=
  positions_perm.nodup_iff.mpr (Finset.nodup_toList _)

theorem positions_complete (position : Position) : position ∈ positions := by
  rw [positions_perm.mem_iff]
  simp

theorem positions_ordered : positions.Pairwise
    (fun first second => rank first ≤ rank second) := by
  simpa only [positions, decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun first second : Position => decide (rank first ≤ rank second))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (Finset.univ : Finset Position).toList)

end SigGolfCandidate.Hypertree.GroupedGraphOrder

end

namespace SigGolfCandidate.Hypertree.GroupedGraphPassive
open SigGolf OracleComp OracleSpec Reference
abbrev Point := GroupedSecurityGraph.Position ⊕
  (BitVec 160 ⊕ (GroupedGlobalPaired.UpperLeafAddress × Fin 52))
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev PointSpec := Point →ₒ BitVec 256
abbrev PointTable := Point → BitVec 256
noncomputable instance : Fintype Point := Fintype.ofFinite Point
noncomputable instance : SampleableType PointTable := SampleableType.ofFintype PointTable

/-- A view can disclose coordinates and guess unopened coordinates adaptively.
Guess success is deliberately not returned to the continuation. -/
inductive Strategy where
  | done
  | reveal (point : Point) (next : BitVec 256 → Strategy)
  | guess (point : Point) (value : Digest) (next : Strategy)
  | coin (n : Nat) (next : Fin (n + 1) → Strategy)
  | bits (next : BitVec 256 → Strategy)
  | collision (target : Digest) (next : BitVec 256 → Strategy)

def complete (cache : QueryCache PointSpec) (table : PointTable) : PointTable :=
  fun point => (cache point).getD (table point)

theorem complete_update (cache : QueryCache PointSpec) (table : PointTable) (point : Point)
    (fresh : cache point = none) (value : BitVec 256) :
    complete (cache.cacheQuery point value) table = complete cache (Function.update table point value) := by
  funext other
  by_cases same : other = point
  · subst other; simp [complete, fresh]
  · simp [complete, same]

theorem cacheQuery_same (cache : QueryCache PointSpec) (point : Point) (value : BitVec 256)
    (present : cache point = some value) : cache.cacheQuery point value = cache := by
  ext other
  by_cases same : other = point
  · subst other; simp [present]
  · simp [same]

/-- The monitor's flag is only output at the end. Its tests never branch the
strategy, so no hidden-coordinate distribution is conditioned on previous misses. -/
noncomputable def play (table : PointTable) : QueryCache PointSpec → Strategy → Nat → ProbComp Bool
  | _, .done, _ => pure false
  | cache, .reveal point next, budget =>
      play table (cache.cacheQuery point (table point)) (next (table point)) budget
  | _, .guess _ _ _, 0 => pure false
  | cache, .guess point value next, budget + 1 => do
      let later ← play table cache next budget
      return decide (cache point = none ∧ truncate (table point) = value) || later
  | _, .collision _ _, 0 => pure false
  | cache, .collision target next, budget + 1 => do
      let answer ← $ᵗ BitVec 256
      let later ← play table cache (next answer) budget
      return decide (truncate answer = target) || later
  | cache, .bits next, budget => do
      let value ← $ᵗ BitVec 256
      play table cache (next value) budget
  | cache, .coin n next, budget => do
      let value ← $ᵗ Fin (n + 1)
      play table cache (next value) budget

noncomputable def experiment (strategy : Strategy) (cache : QueryCache PointSpec) (budget : Nat) : ProbComp Bool := do
  let table ← $ᵗ PointTable
  play (complete cache table) cache strategy budget

/-- Resampling a coordinate preserves the entire table law, including every
randomized continuation. -/
theorem uniform_update_bind {α : Type} (point : Point) (next : PointTable → ProbComp α) :
    𝒮[do
      let answer ← $ᵗ BitVec 256
      let table ← $ᵗ PointTable
      next (Function.update table point answer)] =
      𝒮[do let table ← $ᵗ PointTable; next table] := by
  calc
    _ = 𝒮[do
      let updated ← (do
        let answer ← $ᵗ BitVec 256
        let table ← $ᵗ PointTable
        pure (Function.update table point answer))
      next updated] := by simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]

/-- A fresh reveal can be moved before the uniform completion draw. This is the
invariant-preserving transition at every adaptive opening of a chain point. -/
theorem reveal_fresh (cache : QueryCache PointSpec) (point : Point) (next : BitVec 256 → Strategy)
    (budget : Nat) (fresh : cache point = none) :
    𝒮[experiment (.reveal point next) cache budget] =
      𝒮[do
        let answer ← $ᵗ BitVec 256
        experiment (next answer) (cache.cacheQuery point answer) budget] := by
  unfold experiment
  simp only [play]
  rw [← uniform_update_bind point]
  simp only [complete_update cache _ point fresh, complete, fresh, Option.getD_none,
    Function.update_self]

theorem uniform_point (point : Point) :
    𝒮[(fun table : PointTable => table point) <$> ($ᵗ PointTable)] = 𝒮[$ᵗ BitVec 256] := by
  calc
    _ = 𝒮[do
      let answer ← $ᵗ BitVec 256
      let table ← $ᵗ PointTable
      pure (Function.update table point answer point)] :=
        by simpa only [map_eq_pure_bind] using
          (uniform_update_bind point (fun table => pure (table point))).symm
    _ = 𝒮[do let answer ← $ᵗ BitVec 256; pure answer] := by
      simp only [Function.update_self]
      apply evalSPMF_bind_congr
      intro answer _
      apply evalSPMF_ext
      intro output
      rw [probOutput_bind_const]
      simp
    _ = _ := by simp

/-- A single passive test of an unopened coordinate has exact 128-bit density.
No conditioning on earlier monitor flags appears in this statement. -/
theorem prob_guess_le (cache : QueryCache PointSpec) (point : Point) (value : Digest) :
    Pr[fun table : PointTable => cache point = none ∧ truncate (complete cache table point) = value |
      $ᵗ PointTable] ≤ 1 / 2 ^ 128 := by
  cases present : cache point with
  | some known => simp
  | none =>
    simp only [present, true_and, complete, Option.getD_none]
    change Pr[(fun output : BitVec 256 => truncate output = value) ∘ (fun table : PointTable => table point) |
      $ᵗ PointTable] ≤ _
    rw [← probEvent_map, probEvent_def, uniform_point, ← probEvent_def]
    simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, truncate] using
      (SecurityUniform.prob_extract_mem 128 128 ({value} : Finset Digest)).le

/-- Unconditional union bound for a passive flag. The continuation may depend on
the table, but cannot depend on whether this test succeeded. -/
theorem passive_or_le {α : Type} (draw : ProbComp α) (flag : α → Bool) (next : α → ProbComp Bool) :
    Pr[fun hit => hit = true | (do let value ← draw; let later ← next value; pure (flag value || later))] ≤
      Pr[fun value => flag value = true | draw] + Pr[fun hit => hit = true | draw >>= next] := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | draw] *
        ((if flag value = true then 1 else 0) + Pr[fun hit => hit = true | next value]) := by
      apply ENNReal.tsum_le_tsum
      intro value
      apply mul_le_mul' le_rfl
      cases same : flag value with
      | false => simp
      | true =>
        simp only [Bool.true_or, ↓reduceIte]
        exact probEvent_le_one.trans (le_add_right le_rfl)
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      congr 1
      apply tsum_congr
      intro value
      split_ifs <;> simp

/-- Exact q/2^128 guessing bound for passive tests and fresh output-collision trials, interleaved with arbitrary
coordinate disclosures and private random coins. The monitor is passive, so this
is an unconditional bound rather than a false per-step conditional hazard bound.
A separate scheme simulation must realize its hash-contact tests in this game. -/
theorem prob_experiment_le (strategy : Strategy) (cache : QueryCache PointSpec) (budget : Nat) :
    Pr[fun hit => hit = true | experiment strategy cache budget] ≤ (budget : ENNReal) / 2 ^ 128 := by
  induction strategy generalizing cache budget with
  | done => simp [experiment, play]
  | coin n next ih =>
    have swapped : 𝒮[experiment (.coin n next) cache budget] =
        𝒮[do let value ← $ᵗ Fin (n + 1); experiment (next value) cache budget] := by
      unfold experiment
      simp only [play]
      exact evalSPMF_bind_bind_swap _ _ _
    rw [probEvent_def, swapped, ← probEvent_def]
    exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)
  | bits next ih =>
    have swapped : 𝒮[experiment (.bits next) cache budget] =
        𝒮[do let value ← $ᵗ BitVec 256; experiment (next value) cache budget] := by
      unfold experiment
      simp only [play]
      exact evalSPMF_bind_bind_swap _ _ _
    rw [probEvent_def, swapped, ← probEvent_def]
    exact probEvent_bind_le_of_forall_le (fun value _ => ih value cache budget)
  | reveal point next ih =>
    cases present : cache point with
    | some value =>
      have same : experiment (.reveal point next) cache budget = experiment (next value) cache budget := by
        simp [experiment, play, complete, present, cacheQuery_same cache point value present]
      rw [same]
      exact ih value cache budget
    | none =>
      rw [probEvent_def, reveal_fresh cache point next budget present, ← probEvent_def]
      exact probEvent_bind_le_of_forall_le (fun answer _ => ih answer (cache.cacheQuery point answer) budget)
  | collision target next ih =>
    cases budget with
    | zero => simp [experiment, play]
    | succ budget =>
      have swapped : 𝒮[experiment (.collision target next) cache (budget + 1)] =
          𝒮[do
            let answer ← $ᵗ BitVec 256
            let later ← experiment (next answer) cache budget
            pure (decide (truncate answer = target) || later)] := by
        unfold experiment
        simp only [play, bind_assoc]
        exact evalSPMF_bind_bind_swap _ _ _
      rw [probEvent_def, swapped, ← probEvent_def]
      have bound := passive_or_le ($ᵗ BitVec 256)
        (fun answer => decide (truncate answer = target)) (fun answer => experiment (next answer) cache budget)
      have first : Pr[fun answer : BitVec 256 => decide (truncate answer = target) = true |
          $ᵗ BitVec 256] = 1 / 2 ^ 128 := by
        simpa only [decide_eq_true_eq, Finset.mem_singleton, Finset.card_singleton, Nat.cast_one,
          truncate] using SecurityUniform.prob_extract_mem 128 128 ({target} : Finset Digest)
      have later : Pr[fun hit => hit = true | (do
          let answer ← $ᵗ BitVec 256
          experiment (next answer) cache budget)] ≤ (budget : ENNReal) / 2 ^ 128 :=
        probEvent_bind_le_of_forall_le (fun answer _ => ih answer cache budget)
      calc
        _ ≤ _ := bound
        _ ≤ 1 / 2 ^ 128 + (budget : ENNReal) / 2 ^ 128 := by rw [first]; exact add_le_add le_rfl later
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring
  | guess point value next ih =>
    cases budget with
    | zero => simp [experiment, play]
    | succ budget =>
      have bound := passive_or_le ($ᵗ PointTable)
        (fun table => decide (cache point = none ∧ truncate (complete cache table point) = value))
        (fun table => play (complete cache table) cache next budget)
      change Pr[fun hit => hit = true | (do
        let table ← $ᵗ PointTable
        let later ← play (complete cache table) cache next budget
        pure (decide (cache point = none ∧ truncate (complete cache table point) = value) || later))] ≤ _
      calc
        _ ≤ Pr[fun table : PointTable => cache point = none ∧ truncate (complete cache table point) = value |
              $ᵗ PointTable] + Pr[fun hit => hit = true | experiment next cache budget] := by
                simpa only [decide_eq_true_eq, experiment] using bound
        _ ≤ 1 / 2 ^ 128 + (budget : ENNReal) / 2 ^ 128 :=
          add_le_add (prob_guess_le cache point value) (ih cache budget)
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring


/-- Structural test budget. Reveals and random coins are free; each hidden guess
or independent output-collision trial costs one monitor test. -/
inductive Within : Nat → Strategy → Prop where
  | done (budget : Nat) : Within budget .done
  | reveal {budget : Nat} {point : Point} {next : BitVec 256 → Strategy}
      (bound : ∀ answer, Within budget (next answer)) : Within budget (.reveal point next)
  | guess {budget : Nat} {point : Point} {value : Digest} {next : Strategy}
      (bound : Within budget next) : Within (budget + 1) (.guess point value next)
  | coin {budget n : Nat} {next : Fin (n + 1) → Strategy}
      (bound : ∀ answer, Within budget (next answer)) : Within budget (.coin n next)
  | bits {budget : Nat} {next : BitVec 256 → Strategy}
      (bound : ∀ answer, Within budget (next answer)) : Within budget (.bits next)
  | collision {budget : Nat} {target : Digest} {next : BitVec 256 → Strategy}
      (bound : ∀ answer, Within budget (next answer)) : Within (budget + 1) (.collision target next)
  | weaken {small large : Nat} {strategy : Strategy} (bound : Within small strategy)
      (more : small ≤ large) : Within large strategy

/-- Untruncated passive execution. -/
noncomputable def playAll (table : PointTable) : QueryCache PointSpec → Strategy → ProbComp Bool
  | _, .done => pure false
  | cache, .reveal point next => playAll table (cache.cacheQuery point (table point)) (next (table point))
  | cache, .guess point value next => do
      let later ← playAll table cache next
      return decide (cache point = none ∧ truncate (table point) = value) || later
  | cache, .collision target next => do
      let answer ← $ᵗ BitVec 256
      let later ← playAll table cache (next answer)
      return decide (truncate answer = target) || later
  | cache, .bits next => do
      let value ← $ᵗ BitVec 256
      playAll table cache (next value)
  | cache, .coin n next => do
      let value ← $ᵗ Fin (n + 1)
      playAll table cache (next value)

/-- A proved monitor budget makes its cutoff inert. -/
theorem play_eq_all (table : PointTable) {strategy : Strategy} {limit : Nat}
    (bound : Within limit strategy) (cache : QueryCache PointSpec) (budget : Nat) (enough : limit ≤ budget) :
    play table cache strategy budget = playAll table cache strategy := by
  induction bound generalizing cache budget with
  | done limit => rfl
  | reveal bound ih => exact ih (table _) _ budget enough
  | coin bound ih =>
    simp only [play, playAll]
    apply bind_congr
    intro answer
    exact ih answer cache budget enough
  | bits bound ih =>
    simp only [play, playAll]
    apply bind_congr
    intro answer
    exact ih answer cache budget enough
  | guess bound ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      simp only [play, playAll]
      rw [ih cache budget (by omega)]
  | collision bound ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      simp only [play, playAll]
      apply bind_congr
      intro answer
      rw [ih answer cache budget (by omega)]
  | weaken bound more ih => exact ih cache budget (more.trans enough)

/-- The adaptive bound applies to the actual untruncated monitor once its test
budget has been proved. -/
theorem prob_playAll_le {strategy : Strategy} {budget : Nat} (bound : Within budget strategy)
    (cache : QueryCache PointSpec) :
    Pr[fun hit => hit = true | (do
      let table ← $ᵗ PointTable
      playAll (complete cache table) cache strategy)] ≤ (budget : ENNReal) / 2 ^ 128 := by
  have same : experiment strategy cache budget = (do
      let table ← $ᵗ PointTable
      playAll (complete cache table) cache strategy) := by
    unfold experiment
    apply bind_congr
    intro table
    exact play_eq_all _ bound cache budget le_rfl
  rw [← same]
  exact prob_experiment_le strategy cache budget


end SigGolfCandidate.Hypertree.GroupedGraphPassive
