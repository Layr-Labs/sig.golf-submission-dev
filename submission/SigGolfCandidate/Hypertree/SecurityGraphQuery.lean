import SigGolfCandidate.Hypertree.SecurityGraph
import SigGolfCandidate.Hypertree.SecurityGraphHidden

/-! Inlined from SigGolfCandidate.Hypertree.SecurityGraphReference; its only importer was SigGolfCandidate.Hypertree.SecurityGraphQuery. -/
section
namespace SigGolfCandidate.Hypertree.SecurityGraphReference
open SigGolf Reference SecurityRandomOracle SecurityDerivation SecuritySeparation SecurityGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

def derived (residual : Hash) (secretKey : SecretKey) : Slot → BitVec 256 :=
  fun slot => residual (SecurityDerivation.input secretKey slot)

/-- One full output is planted at each separated canonical graph input. -/
noncomputable def programmed (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash) : Hash :=
  fun query => if found : ∃ position, position.input privateAnswers labels = query
    then labels found.choose else residual query

theorem programmed_graph (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (position : Position) :
    programmed privateAnswers labels residual (position.input privateAnswers labels) = labels position := by
  unfold programmed
  split
  next found =>
    have same : found.choose = position := by
      by_contra different
      exact Position.input_separated privateAnswers _ _ different labels labels found.choose_spec
    rw [same]
  next absent => exact False.elim (absent ⟨position, rfl⟩)

theorem graphInput_not_secretKeyEligible (privateAnswers : Slot → BitVec 256) (position : Position)
    (labels : Labels) : ¬SecretKeyEligible (position.input privateAnswers labels) := by
  cases position with
  | chain address step =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 2 _ _ _ _ _ _ (by decide) (by decide)
  | leaf level tree side =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 3 _ _ _ _ _ _ (by decide) (by decide)
  | node level tree =>
    exact SecurityDomains.not_secretKeyEligible_addressedInput 4 _ _ _ _ _ _ (by decide) (by decide)

/-- Planting public graph labels cannot change either secret-chain derivations or
message-randomizer derivations at any secret key. -/
theorem programmed_private (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (secretKey : SecretKey) (slot : Slot) :
    programmed privateAnswers labels residual (SecurityDerivation.input secretKey slot) =
      residual (SecurityDerivation.input secretKey slot) := by
  unfold programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    exact False.elim (graphInput_not_secretKeyEligible privateAnswers position labels (same ▸ secretKeyEligible_input secretKey slot))
  next absent => rfl

/-- The signer secret is unchanged by graph programming, at the actual reference input. -/
theorem programmed_secret (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress) :
    secret (programmed (derived residual secretKey) labels residual) secretKey address.level.val address.tree.toNat
      address.side address.chain = truncate (derived residual secretKey (.chain address)) := by
  change truncate (programmed (derived residual secretKey) labels residual
    (SecurityDerivation.input secretKey (.chain address))) = _
  rw [programmed_private]
  rfl

/-- Canonical chain points: private source at zero, independent graph label thereafter. -/
def chainPoint (privateAnswers : Slot → BitVec 256) (labels : Labels) (address : ChainAddress)
    (point : Fin 8) : Digest :=
  if zero : point.val = 0 then truncate (privateAnswers (.chain address))
  else truncate (labels (.chain address ⟨point.val - 1, by omega⟩))

theorem programmed_chain_step (privateAnswers : Slot → BitVec 256) (labels : Labels) (residual : Hash)
    (address : ChainAddress) (step : Fin 7) :
    chainHash (programmed privateAnswers labels residual) address.level.val address.tree.toNat
      address.side address.chain step.val (chainPoint privateAnswers labels address ⟨step.val, by omega⟩) =
        truncate (labels (.chain address step)) := by
  change truncate (programmed privateAnswers labels residual
    ((Position.chain address step).input privateAnswers labels)) = _
  rw [programmed_graph]

/-- Every actual reference walk through seven planted steps reads the designated
independent point; this includes every possible WOTS signing digit. -/
theorem programmed_walk (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress)
    (count : Nat) (bound : count ≤ 7) :
    walk (chainHash (programmed (derived residual secretKey) labels residual)
      address.level.val address.tree.toNat address.side address.chain) 0 count
      (secret (programmed (derived residual secretKey) labels residual) secretKey address.level.val
        address.tree.toNat address.side address.chain) =
      chainPoint (derived residual secretKey) labels address ⟨count, by omega⟩ := by
  induction count with
  | zero => simpa only [walk, chainPoint, ↓reduceDIte] using programmed_secret residual secretKey labels address
  | succ count ih =>
    rw [walk_append _ 0 count 1]
    simp only [walk, Nat.zero_add]
    rw [ih (by omega)]
    have step := programmed_chain_step (derived residual secretKey) labels residual address ⟨count, by omega⟩
    simpa only [chainPoint, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel] using step

/-- The exact reference WOTS endpoint is the final canonical chain label. -/
theorem programmed_endpoint (residual : Hash) (secretKey : SecretKey) (labels : Labels) (address : ChainAddress) :
    endpoint (programmed (derived residual secretKey) labels residual) secretKey address.level.val
      address.tree.toNat address.side address.chain = truncate (labels (.chain address 6)) := by
  exact programmed_walk residual secretKey labels address 7 (by decide)

def leafLabel (labels : Labels) (level : Fin 160) (tree : BitVec 192) (side : Bool) : Digest :=
  if level.val = 0 then truncate (labels (.chain ⟨level, tree, side, 0⟩ 0))
  else truncate (labels (.leaf level tree side))

/-- Actual binary-tree leaves recover the sampled graph labels at both the
bottom preimage layer and all upper WOTS layers. -/
theorem programmed_leafRoot (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) :
    leafRoot (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side =
      leafLabel labels level tree side := by
  by_cases bottom : level.val = 0
  · simp only [leafRoot, leafLabel, if_pos bottom]
    rw [programmed_secret residual secretKey labels ⟨level, tree, side, 0⟩]
    exact programmed_chain_step (derived residual secretKey) labels residual ⟨level, tree, side, 0⟩ 0
  · simp only [leafRoot, leafLabel, if_neg bottom]
    have endpoints : endpoint (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side =
        fun chain => truncate (labels (.chain ⟨level, tree, side, chain⟩ 6)) := by
      funext chain
      exact programmed_endpoint residual secretKey labels ⟨level, tree, side, chain⟩
    rw [endpoints]
    change truncate (programmed (derived residual secretKey) labels residual
      ((Position.leaf level tree side).input (derived residual secretKey) labels)) = _
    rw [programmed_graph]

/-- The actual reference public key and every child-tree message are designated
node labels. The probability proof can therefore identify their independence from
WOTS interior points without treating reference hashing as an independent oracle. -/
theorem programmed_treeRoot (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) :
    treeRoot (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat =
      truncate (labels (.node level tree)) := by
  rw [treeRoot, programmed_leafRoot, programmed_leafRoot]
  change truncate (programmed (derived residual secretKey) labels residual
    ((Position.node level tree).input (derived residual secretKey) labels)) = _
  rw [programmed_graph]

/-- Signing reveals exactly the canonical point selected by each WOTS digit. -/
theorem programmed_sign_fragment (residual : Hash) (secretKey : SecretKey) (labels : Labels)
    (level : Fin 160) (tree : BitVec 192) (side : Bool) (message : Digest) (chain : Chain) :
    (signLayer (programmed (derived residual secretKey) labels residual) secretKey level.val tree.toNat side message).values chain =
      if level.val = 0 then chainPoint (derived residual secretKey) labels ⟨level, tree, side, chain⟩ 0
      else chainPoint (derived residual secretKey) labels ⟨level, tree, side, chain⟩ (digit message chain) := by
  by_cases bottom : level.val = 0
  · simp only [signLayer, if_pos bottom]
    exact programmed_secret residual secretKey labels ⟨level, tree, side, chain⟩
  · simp only [signLayer, if_neg bottom]
    exact programmed_walk residual secretKey labels ⟨level, tree, side, chain⟩ (digit message chain).val (by omega)

end SigGolfCandidate.Hypertree.SecurityGraphReference

end

namespace SigGolfCandidate.Hypertree.SecurityGraphQuery
open SigGolf OracleComp OracleSpec Reference SecurityDerivation SecurityGraph
  SecurityGraphSampling SecurityGraphOrder SecurityGraphReference
open scoped Classical

/-- Parse only the public address. The selected vertex does not depend on any
private source or graph label, and arbitrary malformed hash inputs are allowed. -/
noncomputable def locate (query : Query) : Option Position :=
  if found : ∃ position : Position, ∃ payload : List Byte, position.address.input payload = query
  then some found.choose else none

theorem locate_address (position : Position) (payload : List Byte) :
    locate (position.address.input payload) = some position := by
  unfold locate
  split
  next found =>
    obtain ⟨otherPayload, equal⟩ := found.choose_spec
    have same : found.choose = position := Position.address_injective (Address.eq_of_input_eq equal)
    rw [same]
  next absent => exact False.elim (absent ⟨position, payload, rfl⟩)

theorem locate_input (privateAnswers : Slot → BitVec 256) (labels : Labels) (position : Position) :
    locate (position.input privateAnswers labels) = some position :=
  locate_address position (position.payload privateAnswers labels)

/-- At most one canonical graph output can be contacted by any arbitrary hash
query. Address selection is independent of the secret labels being guessed. -/
theorem locate_programmed (privateAnswers : Slot → BitVec 256) (labels : Labels)
    (residual : Hash) (query : Query) :
    programmed privateAnswers labels residual query =
      match locate query with
      | none => residual query
      | some position => if query = position.input privateAnswers labels
          then labels position else residual query := by
  unfold programmed
  split
  next found =>
    have located : locate query = some found.choose := by
      exact (congrArg locate found.choose_spec).symm.trans
        (locate_input privateAnswers labels found.choose)
    simp only [located, if_pos found.choose_spec.symm]
  next absent =>
    cases located : locate query with
    | none => rfl
    | some position =>
      have different : query ≠ position.input privateAnswers labels :=
        fun same => absent ⟨position, same.symm⟩
      simp only [if_neg different]

/-- Cache entries outside the finite canonical graph retain their original value. -/
theorem graphCache_outside (privateAnswers : Slot → BitVec 256) (positions : List Position)
    (labels : Labels) (cache : QueryCache HashSpec) (query : Query)
    (outside : ∀ position ∈ positions, query ≠ position.input privateAnswers labels) :
    graphCache privateAnswers positions labels cache query = cache query := by
  induction positions generalizing cache with
  | nil => rfl
  | cons position rest ih =>
    rw [graphCache, ih _ (fun other member => outside other (List.mem_cons_of_mem _ member))]
    exact QueryCache.cacheQuery_of_ne cache _ (outside position (by simp))

/-- A populated canonical graph cache retains the exact full label at every vertex. -/
theorem graphCache_inside (privateAnswers : Slot → BitVec 256) (positions : List Position)
    (labels : Labels) (cache : QueryCache HashSpec) (position : Position)
    (member : position ∈ positions) :
    graphCache privateAnswers positions labels cache (position.input privateAnswers labels) =
      some (labels position) := by
  induction positions generalizing cache with
  | nil => simp at member
  | cons first rest ih =>
    by_cases occurs : position ∈ rest
    · exact ih _ occurs
    · have same : position = first := (List.mem_cons.mp member).resolve_right occurs
      subst first
      rw [graphCache, graphCache_outside]
      · exact QueryCache.cacheQuery_self _ _ _
      · intro other otherMember equal
        have same : position = other := Position.address_injective (Address.eq_of_input_eq equal)
        exact occurs (same ▸ otherMember)

/-- The real post-sampling cache has precisely one possible canonical contact for
an arbitrary input. This exposes the exact cache lookup used by the lazy oracle. -/
theorem complete_cache_lookup (privateAnswers : Slot → BitVec 256) (labels : Labels) (query : Query) :
    graphCache privateAnswers positions labels ∅ query =
      match locate query with
      | none => none
      | some position => if query = position.input privateAnswers labels
          then some (labels position) else none := by
  cases located : locate query with
  | none =>
    apply graphCache_outside
    intro position _ same
    have wrong := locate_input privateAnswers labels position
    rw [← same, located] at wrong
    cases wrong
  | some position =>
    by_cases same : query = position.input privateAnswers labels
    · simp only [if_pos same]
      rw [same]
      exact graphCache_inside privateAnswers positions labels ∅ position (positions_complete position)
    · simp only [if_neg same]
      apply graphCache_outside
      intro other _ equal
      have otherLocated := locate_input privateAnswers labels other
      rw [← equal, located] at otherLocated
      have positionsEqual := Option.some.inj otherLocated
      exact same (positionsEqual ▸ equal)

end SigGolfCandidate.Hypertree.SecurityGraphQuery
