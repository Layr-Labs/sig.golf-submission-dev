import SigGolfCandidate.Hypertree.GroupedBalancedPrivateDerivation67
import SigGolfCandidate.Hypertree.GroupedPrivateSeparation

/-! A bijective factorization of the eager grouped private oracle table into
bottom sources, upper paired sources, and message randomizers. This makes their
independence a theorem of uniform sampling, rather than a modeling assumption. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPrivateFactors67
open SigGolf OracleComp GroupedBalancedPrivateDerivation67

private def slotCoordinates : Slot →
    BitVec 160 ⊕ ((Fin 150 × BitVec 160 × Fin 34) ⊕ Message)
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
abbrev UpperTable := (Fin 150 × BitVec 160) → Fin 34 → BitVec 256
abbrev NonceTable := Message → BitVec 256
abbrev Factors := BottomTable × (UpperTable × NonceTable)

noncomputable instance : SampleableType PrivateTable := SampleableType.ofFintype PrivateTable
noncomputable instance : SampleableType BottomTable := SampleableType.ofFintype BottomTable
noncomputable instance : SampleableType UpperTable := SampleableType.ofFintype UpperTable
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

end SigGolfCandidate.Hypertree.GroupedBalancedPrivateFactors67
