import SigGolfCandidate.Hypertree.GroupedBalancedGraphPassive67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateFactors67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphReference67

/-! The grouped passive monitor's full-width coordinates are exactly an
independent public-label table, bottom-source table, and ghost-padded upper
chain-source table. The padding changes no WOTS secret value. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorFactors67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67 GroupedBalancedSecurityGraph67 GroupedBalancedGlobalPaired67

abbrev BottomTable := BitVec 160 → BitVec 256
abbrev Factors := GroupedBalancedSecurityGraph67.Labels × (BottomTable × FullSourceTable)

noncomputable instance : Fintype GroupedBalancedSecurityGraph67.Labels :=
  by classical exact Pi.instFintype
instance : Nonempty GroupedBalancedSecurityGraph67.Labels := ⟨fun _ => 0⟩
noncomputable instance : SampleableType GroupedBalancedSecurityGraph67.Labels :=
  SampleableType.ofFintype GroupedBalancedSecurityGraph67.Labels
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
      let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
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

def fromPairs (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable) : PointTable :=
  assemble (labels, (bottom, globalFull (globalSources pairs, ghosts)))

@[simp] theorem public_value (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (position : Position) :
    fromPairs labels bottom pairs ghosts (.inl position) = labels position := rfl

@[simp] theorem bottom_value (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (index : BitVec 160) :
    fromPairs labels bottom pairs ghosts (.inr (.inl index)) = bottom index := rfl

theorem upper_secret_value (labels : GroupedBalancedSecurityGraph67.Labels)
    (bottom : BottomTable) (pairs : PairTable) (ghosts : GhostTable)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    truncate (fromPairs labels bottom pairs ghosts
      (.inr (.inr ((base, leaf), chain)))) =
      GroupedBalancedGraphPayload67.chainSource
        ⟨bottom, fun b l p => pairs (b, l) p⟩ base leaf chain := by
  change (globalFull (globalSources pairs, ghosts) (base, leaf) chain).extractLsb' 0 128 = _
  rw [global_full_truncate]
  simp [GroupedBalancedGlobalPaired67.globalSources,
    GroupedBalancedPairedProjection67.sources_eq_half,
    GroupedBalancedGraphPayload67.chainSource,
    GroupedBalancedGraphPayload67.lowOrHigh,
    SecurityUniform.splitBits]

theorem uniform_fromPairs_bind {α : Type} (next : PointTable → ProbComp α) :
    𝒮[do
      let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
      let bottom ← $ᵗ BottomTable
      let pairs ← $ᵗ PairTable
      let ghosts ← $ᵗ GhostTable
      next (fromPairs labels bottom pairs ghosts)] =
    𝒮[do let table ← $ᵗ PointTable; next table] := by
  calc
    _ = 𝒮[do
      let labels ← $ᵗ GroupedBalancedSecurityGraph67.Labels
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

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorFactors67
