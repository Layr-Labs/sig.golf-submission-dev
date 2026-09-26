import SigGolfCandidate.Hypertree.SecurityGraphMonitorOracle
import SigGolfCandidate.Hypertree.SecurityGraphMonitorStop
import SigGolfCandidate.Hypertree.SecurityGraphAuthorizationDisclosure

/-! Inlined from SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling; its only importer was SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant. -/
section
namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphContact
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphMonitorProgram
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
open scoped Classical

/-- Residual cache entries are safe before the first target contact. This is
needed for repeated inputs: a cache hit does not incur a second fresh-output test. -/
def CacheMiss (table : PointTable) (cache : QueryCache HashSpec) (query : Query) (target : Point) : Prop :=
  ∀ answer, cache query = some answer → truncate answer ≠ truncate (table target)

/-- Exact stopped residual lookup. Fresh answers are tested against the actual
fixed coordinate, regardless of whether it has already been disclosed. -/
theorem stopped_residual {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (query : Query) (target : Point)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree table exposed) (clean : CacheMiss table cache query target) :
    stopped table exposed (SecurityGraphMonitorOracle.residualStep exposed cache query target next) =
      (do
        let result ← (randomOracle (spec := HashSpec) query).run cache
        if truncate result.1 = truncate (table target) then pure none
        else stopped table exposed (next result.1 exposed result.2)) := by
  cases present : cache query with
  | some answer =>
    have miss := clean answer present
    simp only [SecurityGraphMonitorOracle.residualStep, present, randomOracle.run_eq,
      pure_bind, if_neg miss]
  | none =>
    simp only [SecurityGraphMonitorOracle.residualStep, present, randomOracle.run_eq, bind_assoc, pure_bind]
    cases known : exposed target with
    | none => simp only [known, stopped, true_and, eq_comm]
    | some value =>
      have same := agree target value known
      simp only [known, stopped, same]

/-- The exact canonical chain input expressed in the independent point factors. -/
theorem canonical_chain_input (factors : Factors) (address : ChainAddress) (step : Fin 7) :
    (Position.chain address step).input (privateTable factors) (labels factors) =
      chainInput address step (truncate (factors.1 (predecessor address step))) := by
  unfold predecessor
  rw [← assembled_chainPoint factors address ⟨step.val, by omega⟩]
  rfl

/-- Stopped chain semantics in terms of the actual canonical-input predicate.
Unlike the executable passive monitor, this expression may inspect the secret
coordinate, because it is used only in the identical-until-bad coupling. -/
noncomputable def chainStopped {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α) : ProbComp (Option α) :=
  if query = chainInput address step (truncate (table (predecessor address step))) then
    if exposed (predecessor address step) = none then pure none else
      let answer := table (successor address step)
      let opened := exposed.cacheQuery (successor address step) answer
      stopped table opened (next answer opened cache)
  else do
    let result ← (randomOracle (spec := HashSpec) query).run cache
    if truncate result.1 = truncate (table (successor address step)) then pure none
    else stopped table exposed (next result.1 exposed result.2)

theorem stopped_chain {α : Type} (table : PointTable) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (address : ChainAddress) (step : Fin 7) (query : Query)
    (next : BitVec 256 → QueryCache PointSpec → QueryCache HashSpec → Program α)
    (agree : Agree table exposed) (clean : CacheMiss table cache query (successor address step)) :
    stopped table exposed (SecurityGraphMonitorOracle.chainStep exposed cache address step query next) =
      chainStopped table exposed cache address step query next := by
  have residual := stopped_residual table exposed cache query (successor address step) next agree clean
  unfold SecurityGraphMonitorOracle.chainStep chainStopped
  cases parsed : payload address step query with
  | none =>
    have different := payload_none parsed (truncate (table (predecessor address step)))
    simpa only [if_neg different] using residual
  | some point =>
    have canonical := known_matches_canonical table address step query point parsed
    cases known : exposed (predecessor address step) with
    | none =>
      dsimp only
      by_cases hit : point = truncate (table (predecessor address step))
      · have matched := canonical.mpr hit
        have reverse := hit.symm
        simp only [if_pos matched, known, stopped, true_and, reverse, if_true, payload_some parsed]
      · have different := fun same => hit (canonical.mp same)
        have missed : truncate (table (predecessor address step)) ≠ point := Ne.symm hit
        simpa only [if_neg different, stopped, known, true_and, if_neg missed] using residual
    | some value =>
      have same := agree _ value known
      dsimp only
      by_cases hit : point = truncate value
      · have matched := canonical.mpr (hit.trans (congrArg truncate same))
        simp only [if_pos hit, if_pos matched, known, Option.some_ne_none, if_false, stopped]
      · have different : query ≠ chainInput address step (truncate (table (predecessor address step))) := by
          intro matched
          exact hit ((canonical.mp matched).trans (congrArg truncate same.symm))
        simpa only [if_neg hit, if_neg different] using residual

end SigGolfCandidate.Hypertree.SecurityGraphMonitorCoupling

end

namespace SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph SecurityGraphQuery
  SecurityGraphFrontier SecurityGraphPassive SecurityGraphChainMonitor SecurityGraphDisclosure
  SecurityGraphFactor SecurityGraphAuthorization SecurityGraphMonitorCoupling
set_option backward.isDefEq.respectTransparency false
open scoped Classical

/-- Residual cache invariant before the first contact. Every graph-address entry
is both noncanonical and different from that address's fixed truncated target. -/
def ResidualSafe (factors : Factors) (cache : QueryCache HashSpec) : Prop :=
  ∀ query answer, cache query = some answer → ∀ position, locate query = some position →
    query ≠ position.input (privateTable factors) (labels factors) ∧
      truncate answer ≠ truncate (labels factors position)

@[simp] theorem residualSafe_empty (factors : Factors) : ResidualSafe factors ∅ := by
  intro query answer present
  cases present

/-- Repeating an input cannot conceal an old collision: every cached answer was
checked against the same fixed target when it was first inserted. -/
theorem ResidualSafe.chain (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (query : Query) (address : ChainAddress) (step : Fin 7)
    (located : locate query = some (.chain address step)) :
    CacheMiss factors.1 cache query (successor address step) := by
  intro answer present
  exact (safe query answer present (.chain address step) located).2

/-- A fresh noncontact residual answer preserves the invariant for all addresses,
including malformed inputs and addresses other than the updated one. -/
theorem ResidualSafe.cacheQuery (factors : Factors) (cache : QueryCache HashSpec)
    (safe : ResidualSafe factors cache) (query : Query) (answer : BitVec 256)
    (clean : ∀ position, locate query = some position →
      query ≠ position.input (privateTable factors) (labels factors) ∧
        truncate answer ≠ truncate (labels factors position)) :
    ResidualSafe factors (cache.cacheQuery query answer) := by
  intro other value present position located
  by_cases same : other = query
  · subst other
    have values : answer = value := Option.some.inj (by simpa only [QueryCache.cacheQuery_self] using present)
    subst value
    exact clean position located
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other value present position located

/-- Only authorized graph coordinates may be exposed on a contact-free run. -/
def ExposedSafe (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) : Prop :=
  ∀ point value, cache point = some value → Authorized metadata signed point

@[simp] theorem exposedSafe_empty (metadata : MetadataTable) (signed : Finset (BitVec 160)) :
    ExposedSafe metadata signed ∅ := by
  intro point value present
  cases present

theorem ExposedSafe.mono (metadata : MetadataTable) {first second : Finset (BitVec 160)}
    (subset : first ⊆ second) (cache : QueryCache PointSpec) (safe : ExposedSafe metadata first cache) :
    ExposedSafe metadata second cache := by
  intro point value present
  exact authorized_mono metadata subset (safe point value present)

theorem ExposedSafe.cacheQuery (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) (safe : ExposedSafe metadata signed cache)
    (point : Point) (value : BitVec 256) (authorized : Authorized metadata signed point) :
    ExposedSafe metadata signed (cache.cacheQuery point value) := by
  intro other answer present
  by_cases same : other = point
  · subst other; exact authorized
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    exact safe other answer present

/-- A canonical chain step starting at an authorized predecessor exposes only
another authorized point. This also covers all bottom non-source points. -/
theorem authorized_successor (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (address : ChainAddress) (step : Fin 7)
    (known : Authorized metadata signed (predecessor address step)) :
    Authorized metadata signed (successor address step) := by
  by_cases bottom : address.level.val = 0
  · simp only [Authorized, predecessor, successor, bottom, if_true] at *
    exact Or.inl (by omega)
  · simp only [Authorized, predecessor, successor, bottom, if_false] at *
    exact Nat.le_trans known (by omega)

theorem ExposedSafe.hidden (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (cache : QueryCache PointSpec) (safe : ExposedSafe metadata signed cache)
    (point : Point) (unauthorized : ¬Authorized metadata signed point) : cache point = none := by
  cases present : cache point with
  | none => rfl
  | some value => exact False.elim (unauthorized (safe point value present))

theorem ExposedSafe.revealCache (metadata : MetadataTable) (signed : Finset (BitVec 160))
    (table : PointTable) (points : List Point) (cache : QueryCache PointSpec)
    (safe : ExposedSafe metadata signed cache)
    (authorized : ∀ point ∈ points, Authorized metadata signed point) :
    ExposedSafe metadata signed (revealCache table points cache) := by
  induction points generalizing cache with
  | nil => exact safe
  | cons point points ih =>
    exact ih (cache.cacheQuery point (table point))
      (safe.cacheQuery metadata signed cache point (table point) (authorized point (by simp)))
      (fun other member => authorized other (by simp [member]))

end SigGolfCandidate.Hypertree.SecurityGraphMonitorInvariant
