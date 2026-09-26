import SigGolfCandidate.Hypertree.GroupedBalancedPairedProjection67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateFactors67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphOrder67
import SigGolfCandidate.Hypertree.SecurityGraphPassive

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGlobalPaired67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphPassive67. -/
section
/-! Independent 67-chain sources after discarding the spare half of each
34th private pair, lifted over every upper leaf address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGlobalPaired67
open SigGolf OracleComp
open GroupedBalancedPairedProjection67
set_option maxRecDepth 8192

abbrev UpperLeafAddress := Fin 150 × BitVec 160
abbrev PairTable := UpperLeafAddress → Fin 34 → BitVec 256
abbrev SourceTable := UpperLeafAddress → Fin 67 → BitVec 128
abbrev ExtraTable := UpperLeafAddress → BitVec 128
abbrev GhostTable := UpperLeafAddress → Fin 67 → BitVec 128
abbrev FullSourceTable := UpperLeafAddress → Fin 67 → BitVec 256

noncomputable instance : SampleableType SourceTable := SampleableType.ofFintype SourceTable
noncomputable instance : SampleableType ExtraTable := SampleableType.ofFintype ExtraTable
noncomputable instance : SampleableType GhostTable := SampleableType.ofFintype GhostTable
noncomputable instance : SampleableType FullSourceTable := SampleableType.ofFintype FullSourceTable

def globalSources (answers : PairTable) : SourceTable :=
  fun address => GroupedBalancedPairedProjection67.sources (answers address)

def globalSplit (answers : PairTable) : SourceTable × ExtraTable :=
  (globalSources answers,
    fun address => (GroupedBalancedPairedProjection67.splitLast
      (GroupedBalancedPairedSecrets68.sourcesFromPairs (answers address))).2)

def globalUnsplit (parts : SourceTable × ExtraTable) : PairTable :=
  fun address => GroupedBalancedPairedSecrets68.pairsFromSources
    (GroupedBalancedPairedProjection67.addLast (parts.1 address, parts.2 address))

theorem globalUnsplit_split (answers : PairTable) :
    globalUnsplit (globalSplit answers) = answers := by
  funext address
  change GroupedBalancedPairedSecrets68.pairsFromSources
    (GroupedBalancedPairedProjection67.addLast
      (GroupedBalancedPairedProjection67.splitLast
        (GroupedBalancedPairedSecrets68.sourcesFromPairs (answers address)))) =
      answers address
  rw [GroupedBalancedPairedProjection67.addLast_splitLast]
  exact GroupedBalancedPairedSecrets68.tableEquiv.left_inv (answers address)

theorem globalSplit_unsplit (parts : SourceTable × ExtraTable) :
    globalSplit (globalUnsplit parts) = parts := by
  apply Prod.ext
  · funext address
    have localEq : GroupedBalancedPairedProjection67.splitLast
        (GroupedBalancedPairedSecrets68.sourcesFromPairs
          (GroupedBalancedPairedSecrets68.pairsFromSources
            (GroupedBalancedPairedProjection67.addLast
              (parts.1 address, parts.2 address)))) =
        (parts.1 address, parts.2 address) := by
      have inverse := GroupedBalancedPairedSecrets68.tableEquiv.right_inv
        (GroupedBalancedPairedProjection67.addLast
          (parts.1 address, parts.2 address))
      change GroupedBalancedPairedSecrets68.sourcesFromPairs
        (GroupedBalancedPairedSecrets68.pairsFromSources _) = _ at inverse
      rw [inverse]
      exact GroupedBalancedPairedProjection67.splitLast_addLast _
    exact congrArg Prod.fst localEq
  · funext address
    have localEq : GroupedBalancedPairedProjection67.splitLast
        (GroupedBalancedPairedSecrets68.sourcesFromPairs
          (GroupedBalancedPairedSecrets68.pairsFromSources
            (GroupedBalancedPairedProjection67.addLast
              (parts.1 address, parts.2 address)))) =
        (parts.1 address, parts.2 address) := by
      have inverse := GroupedBalancedPairedSecrets68.tableEquiv.right_inv
        (GroupedBalancedPairedProjection67.addLast
          (parts.1 address, parts.2 address))
      change GroupedBalancedPairedSecrets68.sourcesFromPairs
        (GroupedBalancedPairedSecrets68.pairsFromSources _) = _ at inverse
      rw [inverse]
      exact GroupedBalancedPairedProjection67.splitLast_addLast _
    exact congrArg Prod.snd localEq

def globalSplitEquiv : PairTable ≃ (SourceTable × ExtraTable) where
  toFun := globalSplit
  invFun := globalUnsplit
  left_inv := globalUnsplit_split
  right_inv := globalSplit_unsplit

theorem globalSources_unsplit (sources : SourceTable) (extra : ExtraTable) :
    globalSources (globalUnsplit (sources, extra)) = sources :=
  congrArg Prod.fst (globalSplit_unsplit (sources, extra))

theorem uniform_global_sources :
    𝒮[globalSources <$> ($ᵗ PairTable)] = 𝒮[$ᵗ SourceTable] := by
  calc
    _ = 𝒮[Prod.fst <$> (globalSplit <$> ($ᵗ PairTable))] := by
      simp only [Functor.map_map]
      rfl
    _ = 𝒮[Prod.fst <$> ($ᵗ (SourceTable × ExtraTable))] := by
      rw [evalSPMF_map, evalSPMF_map_bijective_uniform_cross
        PairTable globalSplit globalSplitEquiv.bijective, ← evalSPMF_map]
    _ = _ := evalSPMF_map_fst_uniformSample_prod

theorem global_sources_bind {α : Type} (next : SourceTable → ProbComp α) :
    𝒮[do let answers ← $ᵗ PairTable; next (globalSources answers)] =
      𝒮[do let sources ← $ᵗ SourceTable; next sources] := by
  calc
    _ = 𝒮[do let sources ← (globalSources <$> ($ᵗ PairTable)); next sources] := by
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, uniform_global_sources, ← evalSPMF_bind]

def globalFull (parts : SourceTable × GhostTable) : FullSourceTable :=
  fun address chain => parts.2 address chain ++ parts.1 address chain

def globalUnfull (full : FullSourceTable) : SourceTable × GhostTable :=
  (fun address chain =>
      (SecurityUniform.splitBits 128 128 (full address chain)).1,
    fun address chain =>
      (SecurityUniform.splitBits 128 128 (full address chain)).2)

theorem globalUnfull_full (parts : SourceTable × GhostTable) :
    globalUnfull (globalFull parts) = parts := by
  apply Prod.ext
  · funext address chain
    exact BitVec.extractLsb'_append_eq_right
  · funext address chain
    exact BitVec.extractLsb'_append_eq_left

theorem globalFull_unfull (full : FullSourceTable) :
    globalFull (globalUnfull full) = full := by
  funext address chain
  exact (SecurityUniform.splitBits 128 128).symm_apply_apply (full address chain)

def globalFullEquiv : (SourceTable × GhostTable) ≃ FullSourceTable where
  toFun := globalFull
  invFun := globalUnfull
  left_inv := globalUnfull_full
  right_inv := globalFull_unfull

private theorem uniform_pair (A B : Type) [SampleableType A] [SampleableType B] :
    ($ᵗ (A × B)) = (do let first ← $ᵗ A; let second ← $ᵗ B; pure (first, second)) := by
  change ((Prod.mk <$> ($ᵗ A)) <*> ($ᵗ B)) = _
  simp only [seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]

theorem uniform_global_full :
    𝒮[do
      let answers ← $ᵗ PairTable
      let ghosts ← $ᵗ GhostTable
      pure (globalFull (globalSources answers, ghosts))] =
      𝒮[$ᵗ FullSourceTable] := by
  calc
    _ = 𝒮[do
      let sources ← $ᵗ SourceTable
      let ghosts ← $ᵗ GhostTable
      pure (globalFull (sources, ghosts))] := by
        exact global_sources_bind (fun sources => do
          let ghosts ← $ᵗ GhostTable
          pure (globalFull (sources, ghosts)))
    _ = 𝒮[globalFull <$> ($ᵗ (SourceTable × GhostTable))] := by
      simp only [uniform_pair, map_eq_pure_bind, bind_assoc, pure_bind]
    _ = _ := evalSPMF_map_bijective_uniform_cross _ globalFull
      globalFullEquiv.bijective

theorem full_bind {α : Type} (next : FullSourceTable → ProbComp α) :
    𝒮[do
      let answers ← $ᵗ PairTable
      let ghosts ← $ᵗ GhostTable
      next (globalFull (globalSources answers, ghosts))] =
    𝒮[do let full ← $ᵗ FullSourceTable; next full] := by
  calc
    _ = 𝒮[do
      let full ← (do
        let answers ← $ᵗ PairTable
        let ghosts ← $ᵗ GhostTable
        pure (globalFull (globalSources answers, ghosts)))
      next full] := by simp only [bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, uniform_global_full, ← evalSPMF_bind]

theorem global_full_truncate (answers : PairTable) (ghosts : GhostTable)
    (address : UpperLeafAddress) (chain : Fin 67) :
    (globalFull (globalSources answers, ghosts) address chain).extractLsb' 0 128 =
      globalSources answers address chain :=
  BitVec.extractLsb'_append_eq_right

end SigGolfCandidate.Hypertree.GroupedBalancedGlobalPaired67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphPassive67
open SigGolf OracleComp OracleSpec Reference
abbrev Point := GroupedBalancedSecurityGraph67.Position ⊕
  (BitVec 160 ⊕ (GroupedBalancedGlobalPaired67.UpperLeafAddress × Fin 67))
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


end SigGolfCandidate.Hypertree.GroupedBalancedGraphPassive67
