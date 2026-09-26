import SigGolfCandidate.Hypertree.SecurityGraphSigner

/-! Inlined from SigGolfCandidate.Hypertree.SecurityGraphFrontier; its only importer was SigGolfCandidate.Hypertree.SecurityGraphPassive. -/
section
namespace SigGolfCandidate.Hypertree.SecurityGraphFrontier
open SigGolf Reference SecurityDerivation SecurityGraph SecurityGraphReference SecurityGraphIdeal
  SecurityGraphSigner
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev Point := ChainAddress × Fin 8

/-- Public graph metadata. Revealing all these coordinates is conservative: they
contain no upper-chain interior point and no private chain source. Bottom graph
outputs are public preimage targets, while their private sources remain hidden. -/
def MetadataAgree (first second : Labels) : Prop :=
  ∀ position, (match position with
    | .chain address step => address.level.val = 0 ∨ step.val = 6
    | _ => True) → first position = second position

theorem MetadataAgree.node {first second : Labels} (same : MetadataAgree first second)
    (level : Fin 160) (tree : BitVec 192) : first (.node level tree) = second (.node level tree) :=
  same _ trivial

theorem MetadataAgree.leaf {first second : Labels} (same : MetadataAgree first second)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    leafLabel first level tree side = leafLabel second level tree side := by
  unfold leafLabel
  split
  next bottom => rw [same _ (Or.inl bottom)]
  next upper => rw [same _ trivial]

/-- The precise chain points serialized by one layer. -/
def layerPoints (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) : Finset Point :=
  if level.val = 0 then {(⟨level, tree, side, 0⟩, 0)}
  else Finset.univ.image (fun chain : Chain => (⟨level, tree, side, chain⟩, digit message chain))

/-- Modifying every unrevealed source/interior point leaves the actual layer fields
unchanged. The only required point equalities are those explicitly serialized. -/
theorem layer_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (level : Fin 160) (tree : BitVec 192)
    (side : Bool) (message : Digest)
    (revealed : ∀ point ∈ layerPoints level tree side message,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    layer privateFirst first level tree side message = layer privateSecond second level tree side message := by
  unfold layer
  congr 1
  · by_cases bottom : level.val = 0
    · simp only [if_pos bottom]
      funext chain
      split
      next zero =>
        exact revealed (⟨level, tree, side, 0⟩, 0) (by simp [layerPoints, bottom])
      next notZero => rfl
    · simp only [if_neg bottom]
      funext chain
      exact revealed (⟨level, tree, side, chain⟩, digit message chain)
        (by simp [layerPoints, bottom])
  · exact metadata.leaf level tree (!side)

/-- All upper-layer point reveals along the actual signature path. The selection
of each next layer's points depends only on public node metadata. -/
def upperPoints (labels : Labels) :
    (count level index : Nat) → count + level ≤ 160 → index < 2 ^ 192 → Digest → Finset Point
  | 0, _, _, _, _, _ => ∅
  | count + 1, level, index, hl, hi, message =>
      let atLevel : Fin 160 := ⟨level, by omega⟩
      let tree := BitVec.ofNat 192 (index / 2)
      layerPoints atLevel tree (index % 2 == 1) message ∪
        upperPoints labels count (level + 1) (index / 2) (by omega)
          (lt_of_le_of_lt (Nat.div_le_self ..) hi) (truncate (labels (.node atLevel tree)))

/-- Entire upper signing is insensitive to changes outside its revealed points. -/
theorem upper_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (count level index : Nat)
    (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest)
    (revealed : ∀ point ∈ upperPoints first count level index hl hi message,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    upperLayers privateFirst first count level index hl hi message =
      upperLayers privateSecond second count level index hl hi message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [upperLayers]
    apply congrArg₂ List.cons
    · apply layer_congr privateFirst privateSecond first second metadata
      intro point member
      exact revealed point (Finset.mem_union_left _ member)
    · rw [← metadata.node]
      apply ih
      intro point member
      exact revealed point (Finset.mem_union_right _ member)

/-- The reveal set itself is determined by public metadata and the message index,
so choosing which coordinates signing opens does not inspect their hidden values. -/
theorem upperPoints_congr (first second : Labels) (metadata : MetadataAgree first second)
    (count level index : Nat) (hl : count + level ≤ 160) (hi : index < 2 ^ 192) (message : Digest) :
    upperPoints first count level index hl hi message = upperPoints second count level index hl hi message := by
  induction count generalizing level index message with
  | zero => rfl
  | succ count ih =>
    simp only [upperPoints]
    rw [← metadata.node]
    rw [ih]

private theorem index_bound (index : BitVec 160) : index.toNat / 2 < 2 ^ 192 := by
  have bound : (2 : Nat) ^ 160 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
  exact lt_of_le_of_lt (Nat.div_le_self ..) (lt_of_lt_of_le index.isLt bound)

/-- Complete finite point disclosure made by one signature. -/
def signaturePoints (labels : Labels) (index : BitVec 160) : Finset Point :=
  let tree := BitVec.ofNat 192 (index.toNat / 2)
  let side := index.toNat % 2 == 1
  layerPoints 0 tree side 0 ∪
    upperPoints labels 159 1 (index.toNat / 2) (by decide) (index_bound index)
      (truncate (labels (.node 0 tree)))

theorem signaturePoints_congr (first second : Labels) (metadata : MetadataAgree first second)
    (index : BitVec 160) : signaturePoints first index = signaturePoints second index := by
  unfold signaturePoints
  dsimp only
  rw [← metadata.node]
  rw [upperPoints_congr first second metadata]

private theorem compact_congr (r : Bytes 32) {bottom bottom' sibling sibling' : Digest}
    {upper upper' : List LayerSignature} (hb : bottom = bottom') (hs : sibling = sibling')
    (hu : upper = upper') :
    (⟨r, bottom, sibling, upper⟩ : SignatureEncoding.Compact) = ⟨r, bottom', sibling', upper'⟩ := by
  cases hb; cases hs; cases hu; rfl

/-- Complete compact-signature noninterference: unopened chain coordinates can be
changed arbitrarily, while all serialized bytes remain the same. -/
theorem signature_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (r : Bytes 32) (index : BitVec 160)
    (revealed : ∀ point ∈ signaturePoints first index,
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    signature privateFirst first r index = signature privateSecond second r index := by
  unfold signature
  dsimp only
  apply compact_congr
  · apply revealed (⟨0, BitVec.ofNat 192 (index.toNat / 2), index.toNat % 2 == 1, 0⟩, 0)
    apply Finset.mem_union_left
    simp [layerPoints]
  · exact metadata.leaf _ _ _
  · rw [← metadata.node]
    apply upper_congr privateFirst privateSecond first second metadata
    intro point member
    exact revealed point (Finset.mem_union_right _ member)

/-- Noninterference stated directly for the actual monadic signer, including its
secret deterministic randomizer and its actual residual-oracle message index. -/
theorem signer_congr (privateFirst privateSecond : PrivateTable) (first second : Labels)
    (metadata : MetadataAgree first second) (residual : Hash) (message : Message)
    (nonce : privateFirst (.randomizer message) = privateSecond (.randomizer message))
    (revealed : ∀ point ∈ signaturePoints first
        ((residual (SecurityRandomOracle.indexInput message (privateFirst (.randomizer message)))).extractLsb' 0 160),
      chainPoint privateFirst first point.1 point.2 = chainPoint privateSecond second point.1 point.2) :
    evalWithAnswerFn (answers privateFirst (programmed privateFirst first residual))
      (SecurityIdealSign.signCompact message) =
    evalWithAnswerFn (answers privateSecond (programmed privateSecond second residual))
      (SecurityIdealSign.signCompact message) := by
  rw [eval_signCompact, eval_signCompact, ← nonce]
  exact signature_congr privateFirst privateSecond first second metadata _ _ revealed


end SigGolfCandidate.Hypertree.SecurityGraphFrontier

end

namespace SigGolfCandidate.Hypertree.SecurityGraphPassive
open SigGolf OracleComp OracleSpec Reference SecurityGraphFrontier
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


end SigGolfCandidate.Hypertree.SecurityGraphPassive
