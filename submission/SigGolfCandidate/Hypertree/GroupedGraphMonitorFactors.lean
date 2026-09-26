import SigGolfCandidate.Hypertree.GroupedGraphPayload
import SigGolfCandidate.Hypertree.GroupedMixedScheme
import SigGolfCandidate.Hypertree.GroupedGraphMonitorProgram
import SigGolfCandidate.Hypertree.GroupedPrivateSeparation
import SigGolfCandidate.Hypertree.GroupedGlobalPaired

/-! Inlined from SigGolfCandidate.Hypertree.GroupedPrivateFactors; its only importer was SigGolfCandidate.Hypertree.GroupedGraphMonitorFactors. -/
section
/-! A bijective factorization of the eager grouped private oracle table into
bottom sources, upper paired sources, and message randomizers. This makes their
independence a theorem of uniform sampling, rather than a modeling assumption. -/

namespace SigGolfCandidate.Hypertree.GroupedPrivateFactors
open SigGolf OracleComp GroupedPrivateDerivation

private def slotCoordinates : Slot →
    BitVec 160 ⊕ ((Fin 150 × BitVec 160 × Fin 26) ⊕ Message)
  | .bottom index => .inl index
  | .upper base leaf pair => .inr (.inl (base, leaf, pair))
  | .randomizer message => .inr (.inr message)

private theorem slotCoordinates_injective : Function.Injective slotCoordinates := by
  intro first second same
  cases first <;> cases second <;> simp_all [slotCoordinates]

instance : Finite Slot := Finite.of_injective _ slotCoordinates_injective
noncomputable instance : Fintype Slot := Fintype.ofFinite Slot

abbrev PrivateTable := Slot → BitVec 256
abbrev BottomTable := BitVec 160 → BitVec 256
abbrev UpperTable := GroupedGlobalPaired.PairTable
abbrev NonceTable := Message → BitVec 256
abbrev Factors := BottomTable × (UpperTable × NonceTable)

noncomputable instance : SampleableType PrivateTable := SampleableType.ofFintype PrivateTable
noncomputable instance : SampleableType BottomTable := SampleableType.ofFintype BottomTable
noncomputable instance : SampleableType NonceTable := SampleableType.ofFintype NonceTable

def factor (answers : PrivateTable) : Factors :=
  (fun index => answers (.bottom index),
    (fun address pair => answers (.upper address.1 address.2 pair),
      fun message => answers (.randomizer message)))

def assemble (factors : Factors) : PrivateTable
  | .bottom index => factors.1 index
  | .upper base leaf pair => factors.2.1 (base, leaf) pair
  | .randomizer message => factors.2.2 message

def tableEquiv : PrivateTable ≃ Factors where
  toFun := factor
  invFun := assemble
  left_inv := by
    intro answers
    funext slot
    cases slot <;> rfl
  right_inv := by
    intro factors
    apply Prod.ext
    · funext index
      rfl
    · apply Prod.ext
      · funext address pair
        rcases address with ⟨base, leaf⟩
        rfl
      · funext message
        rfl

theorem uniform_private_factors :
    𝒮[factor <$> ($ᵗ PrivateTable)] = 𝒮[$ᵗ Factors] :=
  evalSPMF_map_bijective_uniform_cross PrivateTable factor tableEquiv.bijective

private theorem uniform_pair (A B : Type) [SampleableType A] [SampleableType B] :
    ($ᵗ (A × B)) = (do let first ← $ᵗ A; let second ← $ᵗ B; pure (first, second)) := by
  change ((Prod.mk <$> ($ᵗ A)) <*> ($ᵗ B)) = _
  simp only [seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]

theorem independent_private_factors :
    𝒮[do let answers ← $ᵗ PrivateTable; pure (factor answers)] =
    𝒮[do
      let bottom ← $ᵗ BottomTable
      let upper ← $ᵗ UpperTable
      let nonces ← $ᵗ NonceTable
      pure (bottom, (upper, nonces))] := by
  simpa only [uniform_pair, map_eq_pure_bind, bind_assoc, pure_bind]
    using uniform_private_factors

theorem independent_bind {α : Type} (next : Factors → ProbComp α) :
    𝒮[do let answers ← $ᵗ PrivateTable; next (factor answers)] =
    𝒮[do
      let bottom ← $ᵗ BottomTable
      let upper ← $ᵗ UpperTable
      let nonces ← $ᵗ NonceTable
      next (bottom, (upper, nonces))] := by
  calc
    _ = 𝒮[do
      let factors ← (do let answers ← $ᵗ PrivateTable; pure (factor answers))
      next factors] := by simp only [bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, independent_private_factors, ← evalSPMF_bind]
      simp only [bind_assoc, pure_bind]

end SigGolfCandidate.Hypertree.GroupedPrivateFactors
end

/-! Bridges from the grouped graph's private-answer tables to the actual
tree-addressed functional signer and public hash queries. -/

namespace SigGolfCandidate.Hypertree.GroupedGraphReference
open SigGolf Reference SecurityRandomOracle GroupedSecurityGraph GroupedGraphPayload

def sourceAnswers (hash : Hash) (secretKey : SecretKey) : PrivateAnswers where
  bottom := fun index => hash (GroupedBottomIndex.sourceInput secretKey index)
  upper := fun base leaf pair =>
    hash (GroupedAddressDomains.upperInput secretKey
      ⟨base.val + 10, by have := base.isLt; omega⟩ leaf pair)

theorem bottom_source_value (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) :
    truncate ((sourceAnswers hash secretKey).bottom index) =
      GroupedBottomTree.secret hash secretKey index.toNat := by
  rfl

theorem upper_source_value (hash : Hash) (secretKey : SecretKey)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 52) :
    chainSource (sourceAnswers hash secretKey) base leaf chain =
      GroupedUpperTree.secret hash secretKey (base.val + 10) leaf.toNat chain := by
  rfl

theorem bottom_leaf_graph_input (hash : Hash) (secretKey : SecretKey)
    (labels : Labels) (index : BitVec 160) :
    (bottomLeaf index).input
      (payload (sourceAnswers hash secretKey) labels (bottomLeaf index)) =
    addressedInput 2 0 index.toNat 0 0 0
      (bytes (GroupedBottomTree.secret hash secretKey index.toNat)) := by
  rw [bottom_leaf_payload, bottom_leaf_input, bottom_source_value]

theorem upper_chain_zero_graph_input (hash : Hash) (secretKey : SecretKey)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) :
    (upperChain base leaf chain 0).input
      (payload (sourceAnswers hash secretKey) labels (upperChain base leaf chain 0)) =
    addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val 0
      (bytes (GroupedUpperTree.secret hash secretKey (base.val + 10) leaf.toNat chain)) := by
  rw [upper_chain_zero_payload, upper_chain_input, upper_source_value]
  rfl

theorem upper_chain_step_graph_input (privateAnswers : PrivateAnswers)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 52) (step : Fin 4) :
    (upperChain base leaf chain ⟨step.val + 1, by omega⟩).input
      (payload privateAnswers labels
        (upperChain base leaf chain ⟨step.val + 1, by omega⟩)) =
    addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val (step.val + 1)
      (bytes (truncate (labels
        (upperChain base leaf chain ⟨step.val, by omega⟩)))) := by
  rw [upper_chain_step_payload, upper_chain_input]

theorem upper_leaf_graph_input (privateAnswers : PrivateAnswers)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160) :
    (upperLeaf base leaf).input (payload privateAnswers labels (upperLeaf base leaf)) =
    addressedInput 3 (base.val + 10) leaf.toNat 0 0 0
      ((List.ofFn (fun chain : Fin 52 =>
        truncate (labels (upperChain base leaf chain ⟨4, by decide⟩)))).flatMap bytes) := by
  rw [upper_leaf_payload, upper_leaf_input]

end SigGolfCandidate.Hypertree.GroupedGraphReference


/-! The grouped passive monitor's full-width coordinates are exactly an
independent public-label table, bottom-source table, and ghost-padded upper
chain-source table. The padding changes no WOTS secret value. -/

namespace SigGolfCandidate.Hypertree.GroupedGraphMonitorFactors
open SigGolf OracleComp OracleSpec Reference
open GroupedGraphPassive GroupedSecurityGraph GroupedGlobalPaired

abbrev BottomTable := BitVec 160 → BitVec 256
abbrev Factors := GroupedSecurityGraph.Labels × (BottomTable × FullSourceTable)

noncomputable instance : Fintype GroupedSecurityGraph.Labels :=
  by classical exact Pi.instFintype
instance : Nonempty GroupedSecurityGraph.Labels := ⟨fun _ => 0⟩
noncomputable instance : SampleableType GroupedSecurityGraph.Labels :=
  SampleableType.ofFintype GroupedSecurityGraph.Labels
noncomputable instance : SampleableType BottomTable :=
  SampleableType.ofFintype BottomTable
noncomputable instance : SampleableType GhostTable :=
  SampleableType.ofFintype GhostTable

def factor (table : PointTable) : Factors :=
  (fun position => table (.inl position),
    (fun index => table (.inr (.inl index)),
      fun address chain => table (.inr (.inr (address, chain)))))

def assemble (factors : Factors) : PointTable
  | .inl position => factors.1 position
  | .inr (.inl index) => factors.2.1 index
  | .inr (.inr (address, chain)) => factors.2.2 address chain

theorem assemble_factor (table : PointTable) : assemble (factor table) = table := by
  funext point
  cases point with
  | inl position => rfl
  | inr rest =>
      cases rest with
      | inl index => rfl
      | inr upper =>
          rcases upper with ⟨address, chain⟩
          rfl

theorem factor_assemble (factors : Factors) : factor (assemble factors) = factors := by
  apply Prod.ext
  · funext position
    rfl
  · apply Prod.ext
    · funext index
      rfl
    · funext address chain
      rfl

def tableEquiv : PointTable ≃ Factors where
  toFun := factor
  invFun := assemble
  left_inv := assemble_factor
  right_inv := factor_assemble

theorem uniform_factor :
    𝒮[factor <$> ($ᵗ PointTable)] = 𝒮[$ᵗ Factors] :=
  evalSPMF_map_bijective_uniform_cross PointTable factor tableEquiv.bijective

private theorem uniform_pair (A B : Type) [SampleableType A] [SampleableType B] :
    ($ᵗ (A × B)) = (do let first ← $ᵗ A; let second ← $ᵗ B; pure (first, second)) := by
  change ((Prod.mk <$> ($ᵗ A)) <*> ($ᵗ B)) = _
  simp only [seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]

theorem independent_bind {α : Type} (next : Factors → ProbComp α) :
    𝒮[do let table ← $ᵗ PointTable; next (factor table)] =
    𝒮[do
      let labels ← $ᵗ GroupedSecurityGraph.Labels
      let bottom ← $ᵗ BottomTable
      let upper ← $ᵗ FullSourceTable
      next (labels, (bottom, upper))] := by
  calc
    _ = 𝒮[do let factors ← (factor <$> ($ᵗ PointTable)); next factors] := by
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    _ = 𝒮[do let factors ← ($ᵗ Factors); next factors] := by
      rw [evalSPMF_bind, uniform_factor, ← evalSPMF_bind]
    _ = _ := by
      simp only [uniform_pair, bind_assoc, pure_bind]

def fromPairs (labels : GroupedSecurityGraph.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable) : PointTable :=
  assemble (labels, (bottom, globalFull (pairs, ghosts)))

@[simp] theorem public_value (labels : GroupedSecurityGraph.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (position : Position) :
    fromPairs labels bottom pairs ghosts (.inl position) = labels position := rfl

@[simp] theorem bottom_value (labels : GroupedSecurityGraph.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (index : BitVec 160) :
    fromPairs labels bottom pairs ghosts (.inr (.inl index)) = bottom index := rfl

theorem upper_secret_value (labels : GroupedSecurityGraph.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 52) :
    truncate (fromPairs labels bottom pairs ghosts
      (.inr (.inr ((base, leaf), chain)))) =
      GroupedGraphPayload.chainSource
        ⟨bottom, fun b l p => pairs (b, l) p⟩ base leaf chain := by
  exact global_full_truncate pairs ghosts (base, leaf) chain

theorem uniform_fromPairs_bind {α : Type} (next : PointTable → ProbComp α) :
    𝒮[do
      let labels ← $ᵗ GroupedSecurityGraph.Labels
      let bottom ← $ᵗ BottomTable
      let pairs ← $ᵗ PairTable
      let ghosts ← $ᵗ GhostTable
      next (fromPairs labels bottom pairs ghosts)] =
    𝒮[do let table ← $ᵗ PointTable; next table] := by
  calc
    _ = 𝒮[do
      let labels ← $ᵗ GroupedSecurityGraph.Labels
      let bottom ← $ᵗ BottomTable
      let tables ← $ᵗ (PairTable × GhostTable)
      next (assemble (labels, (bottom, globalFull tables)))] := by
        simp only [uniform_pair, bind_assoc, pure_bind, fromPairs]
    _ = 𝒮[do
      let labels ← $ᵗ GroupedSecurityGraph.Labels
      let bottom ← $ᵗ BottomTable
      let upper ← $ᵗ FullSourceTable
      next (assemble (labels, (bottom, upper)))] := by
        apply evalSPMF_bind_congr
        intro labels _
        apply evalSPMF_bind_congr
        intro bottom _
        exact full_bind (fun upper => next (assemble (labels, (bottom, upper))))
    _ = _ := by
      have same := independent_bind (fun factors => next (assemble factors))
      simp only [assemble_factor] at same
      exact same.symm

end SigGolfCandidate.Hypertree.GroupedGraphMonitorFactors
