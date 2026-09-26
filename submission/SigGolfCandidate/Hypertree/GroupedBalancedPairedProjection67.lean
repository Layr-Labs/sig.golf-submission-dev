import SigGolfCandidate.Hypertree.SecurityUniform

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedPairedSecrets68; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPairedProjection67. -/
section
/-! A table of 34 independent 256-bit answers is exactly a table of 68
independent 128-bit WOTS sources after splitting each answer in half. This
isolated lemma is the probability bridge for the paired-secret design. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPairedSecrets68
open SigGolf OracleComp SecurityUniform
set_option maxHeartbeats 0

def pairOf (chain : Fin 68) : Fin 34 := ⟨chain.val / 2, by omega⟩
def evenOf (pair : Fin 34) : Fin 68 := ⟨2 * pair.val, by omega⟩
def oddOf (pair : Fin 34) : Fin 68 := ⟨2 * pair.val + 1, by omega⟩

def sourcesFromPairs (answers : Fin 34 → BitVec 256) (chain : Fin 68) : BitVec 128 :=
  if chain.val % 2 = 0 then (splitBits 128 128 (answers (pairOf chain))).1
  else (splitBits 128 128 (answers (pairOf chain))).2

def pairsFromSources (sources : Fin 68 → BitVec 128) (pair : Fin 34) : BitVec 256 :=
  (splitBits 128 128).symm (sources (evenOf pair), sources (oddOf pair))

private theorem pair_even (pair : Fin 34) : pairOf (evenOf pair) = pair :=
  Fin.ext (by simp [pairOf, evenOf])

private theorem pair_odd (pair : Fin 34) : pairOf (oddOf pair) = pair :=
  Fin.ext (by simp [pairOf, oddOf]; omega)

private theorem even_mod (pair : Fin 34) : (evenOf pair).val % 2 = 0 := by
  simp [evenOf]

private theorem odd_mod (pair : Fin 34) : (oddOf pair).val % 2 ≠ 0 := by
  simp [oddOf]

private theorem even_pair (chain : Fin 68) (h : chain.val % 2 = 0) :
    evenOf (pairOf chain) = chain := Fin.ext (by simp [evenOf, pairOf]; omega)

private theorem odd_pair (chain : Fin 68) (h : chain.val % 2 ≠ 0) :
    oddOf (pairOf chain) = chain := Fin.ext (by simp [oddOf, pairOf]; omega)

def tableEquiv : (Fin 34 → BitVec 256) ≃ (Fin 68 → BitVec 128) where
  toFun := sourcesFromPairs
  invFun := pairsFromSources
  left_inv := by
    intro answers
    funext pair
    apply (splitBits 128 128).injective
    simp [pairsFromSources, sourcesFromPairs, pair_even, pair_odd, even_mod, odd_mod]
  right_inv := by
    intro sources
    funext chain
    by_cases h : chain.val % 2 = 0
    · rw [← even_pair chain h]
      simp [sourcesFromPairs, pairsFromSources, pair_even, even_mod]
    · rw [← odd_pair chain h]
      simp [sourcesFromPairs, pairsFromSources, pair_odd, odd_mod]

theorem uniform_sources :
    𝒮[sourcesFromPairs <$> ($ᵗ (Fin 34 → BitVec 256))] =
      𝒮[$ᵗ (Fin 68 → BitVec 128)] :=
  evalSPMF_map_bijective_uniform_cross _ sourcesFromPairs tableEquiv.bijective

/-! The high halves of the following full-width source table are proof-only
ghost randomness. Honest WOTS code reads just `truncate`, so this table has
the same visible chain secrets as the paired-answer implementation. -/

def withGhosts (answers : Fin 34 → BitVec 256) (ghosts : Fin 68 → BitVec 128) :
    Fin 68 → BitVec 256 :=
  fun chain => ghosts chain ++ sourcesFromPairs answers chain

def fullTableEquiv :
    ((Fin 34 → BitVec 256) × (Fin 68 → BitVec 128)) ≃ (Fin 68 → BitVec 256) where
  toFun := fun tables => withGhosts tables.1 tables.2
  invFun := fun table =>
    (pairsFromSources (fun chain => (splitBits 128 128 (table chain)).1),
      fun chain => (splitBits 128 128 (table chain)).2)
  left_inv := by
    intro tables
    apply Prod.ext
    · change pairsFromSources (fun chain =>
        (splitBits 128 128 (withGhosts tables.1 tables.2 chain)).1) = tables.1
      have h : (fun chain =>
          (splitBits 128 128 (withGhosts tables.1 tables.2 chain)).1) =
          sourcesFromPairs tables.1 := by
        funext chain
        exact BitVec.extractLsb'_append_eq_right
      rw [h]
      exact tableEquiv.left_inv tables.1
    · funext chain
      exact BitVec.extractLsb'_append_eq_left
  right_inv := by
    intro table
    funext chain
    change (splitBits 128 128 (table chain)).2 ++
      sourcesFromPairs
        (pairsFromSources (fun index => (splitBits 128 128 (table index)).1)) chain =
      table chain
    have h := congrFun
      (tableEquiv.right_inv (fun index => (splitBits 128 128 (table index)).1)) chain
    change sourcesFromPairs
      (pairsFromSources (fun index => (splitBits 128 128 (table index)).1)) chain =
      (splitBits 128 128 (table chain)).1 at h
    rw [h]
    exact (splitBits 128 128).symm_apply_apply (table chain)

theorem uniform_with_ghosts :
    𝒮[fullTableEquiv <$>
      ($ᵗ ((Fin 34 → BitVec 256) × (Fin 68 → BitVec 128)))] =
      𝒮[$ᵗ (Fin 68 → BitVec 256)] :=
  evalSPMF_map_bijective_uniform_cross _ fullTableEquiv fullTableEquiv.bijective

theorem withGhosts_truncate (answers : Fin 34 → BitVec 256)
    (ghosts : Fin 68 → BitVec 128) (chain : Fin 68) :
    (withGhosts answers ghosts chain).extractLsb' 0 128 =
      sourcesFromPairs answers chain := by
  exact BitVec.extractLsb'_append_eq_right

end SigGolfCandidate.Hypertree.GroupedBalancedPairedSecrets68

end

/-! Thirty-four paired answers yield 68 independent halves. The direct
signature uses the first 67; the unused final half is marginalized away. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPairedProjection67
open SigGolf OracleComp GroupedBalancedPairedSecrets68 SecurityUniform
set_option maxRecDepth 8192

abbrev PairTable := Fin 34 → BitVec 256
abbrev SourceTable := Fin 67 → BitVec 128
abbrev GhostTable := Fin 67 → BitVec 128
abbrev FullTable := Fin 67 → BitVec 256

noncomputable instance : SampleableType SourceTable := SampleableType.ofFintype SourceTable
noncomputable instance : SampleableType GhostTable := SampleableType.ofFintype GhostTable
noncomputable instance : SampleableType FullTable := SampleableType.ofFintype FullTable

def take67 (full : Fin 68 → BitVec 128) : SourceTable :=
  fun chain => full ⟨chain.val, by have := chain.isLt; omega⟩

def splitLast (full : Fin 68 → BitVec 128) : SourceTable × BitVec 128 :=
  (take67 full, full ⟨67, by decide⟩)

def addLast (parts : SourceTable × BitVec 128) : Fin 68 → BitVec 128 :=
  fun chain => if low : chain.val < 67 then parts.1 ⟨chain.val, low⟩ else parts.2

theorem addLast_splitLast (full : Fin 68 → BitVec 128) :
    addLast (splitLast full) = full := by
  funext chain
  by_cases low : chain.val < 67
  · simp only [addLast, dif_pos low, splitLast, take67]
  · have lastVal : chain.val = 67 := by have := chain.isLt; omega
    have last : chain = (⟨67, by decide⟩ : Fin 68) := by
      apply Fin.ext
      exact lastVal
    subst chain
    simp [addLast, splitLast]

theorem splitLast_addLast (parts : SourceTable × BitVec 128) :
    splitLast (addLast parts) = parts := by
  apply Prod.ext
  · funext chain
    simp [splitLast, take67, addLast, chain.isLt]
  · simp [splitLast, addLast]

def splitLastEquiv : (Fin 68 → BitVec 128) ≃ (SourceTable × BitVec 128) where
  toFun := splitLast
  invFun := addLast
  left_inv := addLast_splitLast
  right_inv := splitLast_addLast

theorem uniform_prefix :
    𝒮[take67 <$> ($ᵗ (Fin 68 → BitVec 128))] = 𝒮[$ᵗ SourceTable] := by
  calc
    _ = 𝒮[Prod.fst <$> (splitLast <$> ($ᵗ (Fin 68 → BitVec 128)))] := by
      simp only [Functor.map_map]
      rfl
    _ = 𝒮[Prod.fst <$> ($ᵗ (SourceTable × BitVec 128))] := by
      rw [evalSPMF_map, evalSPMF_map_bijective_uniform_cross
        (Fin 68 → BitVec 128) splitLast splitLastEquiv.bijective,
        ← evalSPMF_map]
    _ = _ := evalSPMF_map_fst_uniformSample_prod

def sources (answers : PairTable) : SourceTable :=
  take67 (GroupedBalancedPairedSecrets68.sourcesFromPairs answers)

theorem sources_eq_half (answers : PairTable) (chain : Fin 67) :
    sources answers chain =
      if chain.val % 2 = 0 then
        (splitBits 128 128 (answers ⟨chain.val / 2, by have := chain.isLt; omega⟩)).1
      else
        (splitBits 128 128 (answers ⟨chain.val / 2, by have := chain.isLt; omega⟩)).2 := rfl

theorem uniform_sources :
    𝒮[sources <$> ($ᵗ PairTable)] = 𝒮[$ᵗ SourceTable] := by
  calc
    _ = 𝒮[take67 <$> (GroupedBalancedPairedSecrets68.sourcesFromPairs <$> ($ᵗ PairTable))] := by
      simp only [Functor.map_map]
      rfl
    _ = 𝒮[take67 <$> ($ᵗ (Fin 68 → BitVec 128))] := by
      simp only [evalSPMF_map]
      have h := GroupedBalancedPairedSecrets68.uniform_sources
      simp only [evalSPMF_map] at h
      rw [h]
    _ = _ := uniform_prefix

theorem sources_bind {α : Type} (next : SourceTable → ProbComp α) :
    𝒮[do let answers ← $ᵗ PairTable; next (sources answers)] =
      𝒮[do let source ← $ᵗ SourceTable; next source] := by
  calc
    _ = 𝒮[do let source ← (sources <$> ($ᵗ PairTable)); next source] := by
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, uniform_sources, ← evalSPMF_bind]

def joinGhost (parts : SourceTable × GhostTable) : FullTable :=
  fun chain => parts.2 chain ++ parts.1 chain

def splitGhost (full : FullTable) : SourceTable × GhostTable :=
  (fun chain => (splitBits 128 128 (full chain)).1,
    fun chain => (splitBits 128 128 (full chain)).2)

theorem splitGhost_joinGhost (parts : SourceTable × GhostTable) :
    splitGhost (joinGhost parts) = parts := by
  apply Prod.ext
  · funext chain
    exact BitVec.extractLsb'_append_eq_right
  · funext chain
    exact BitVec.extractLsb'_append_eq_left

theorem joinGhost_splitGhost (full : FullTable) :
    joinGhost (splitGhost full) = full := by
  funext chain
  exact (splitBits 128 128).symm_apply_apply (full chain)

def ghostEquiv : (SourceTable × GhostTable) ≃ FullTable where
  toFun := joinGhost
  invFun := splitGhost
  left_inv := splitGhost_joinGhost
  right_inv := joinGhost_splitGhost

theorem uniform_full_sources :
    𝒮[joinGhost <$> ($ᵗ (SourceTable × GhostTable))] =
      𝒮[$ᵗ FullTable] :=
  evalSPMF_map_bijective_uniform_cross _ joinGhost ghostEquiv.bijective

end SigGolfCandidate.Hypertree.GroupedBalancedPairedProjection67
