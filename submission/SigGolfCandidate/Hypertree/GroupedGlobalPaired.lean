import SigGolfCandidate.Hypertree.SecurityUniform

/-! Inlined from SigGolfCandidate.Hypertree.GroupedPairedSecrets; its only importer was SigGolfCandidate.Hypertree.GroupedGlobalPaired. -/
section
/-! A table of 26 independent 256-bit answers is exactly a table of 52
independent 128-bit WOTS sources after splitting each answer in half. This
isolated lemma is the probability bridge for the paired-secret design. -/

namespace SigGolfCandidate.Hypertree.GroupedPairedSecrets
open SigGolf OracleComp SecurityUniform
set_option maxHeartbeats 0

def pairOf (chain : Fin 52) : Fin 26 := ⟨chain.val / 2, by omega⟩
def evenOf (pair : Fin 26) : Fin 52 := ⟨2 * pair.val, by omega⟩
def oddOf (pair : Fin 26) : Fin 52 := ⟨2 * pair.val + 1, by omega⟩

def sourcesFromPairs (answers : Fin 26 → BitVec 256) (chain : Fin 52) : BitVec 128 :=
  if chain.val % 2 = 0 then (splitBits 128 128 (answers (pairOf chain))).1
  else (splitBits 128 128 (answers (pairOf chain))).2

def pairsFromSources (sources : Fin 52 → BitVec 128) (pair : Fin 26) : BitVec 256 :=
  (splitBits 128 128).symm (sources (evenOf pair), sources (oddOf pair))

private theorem pair_even (pair : Fin 26) : pairOf (evenOf pair) = pair :=
  Fin.ext (by simp [pairOf, evenOf])

private theorem pair_odd (pair : Fin 26) : pairOf (oddOf pair) = pair :=
  Fin.ext (by simp [pairOf, oddOf]; omega)

private theorem even_mod (pair : Fin 26) : (evenOf pair).val % 2 = 0 := by
  simp [evenOf]

private theorem odd_mod (pair : Fin 26) : (oddOf pair).val % 2 ≠ 0 := by
  simp [oddOf]

private theorem even_pair (chain : Fin 52) (h : chain.val % 2 = 0) :
    evenOf (pairOf chain) = chain := Fin.ext (by simp [evenOf, pairOf]; omega)

private theorem odd_pair (chain : Fin 52) (h : chain.val % 2 ≠ 0) :
    oddOf (pairOf chain) = chain := Fin.ext (by simp [oddOf, pairOf]; omega)

def tableEquiv : (Fin 26 → BitVec 256) ≃ (Fin 52 → BitVec 128) where
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
    𝒮[sourcesFromPairs <$> ($ᵗ (Fin 26 → BitVec 256))] =
      𝒮[$ᵗ (Fin 52 → BitVec 128)] :=
  evalSPMF_map_bijective_uniform_cross _ sourcesFromPairs tableEquiv.bijective

/-! The high halves of the following full-width source table are proof-only
ghost randomness. Honest WOTS code reads just `truncate`, so this table has
the same visible chain secrets as the paired-answer implementation. -/

def withGhosts (answers : Fin 26 → BitVec 256) (ghosts : Fin 52 → BitVec 128) :
    Fin 52 → BitVec 256 :=
  fun chain => ghosts chain ++ sourcesFromPairs answers chain

def fullTableEquiv :
    ((Fin 26 → BitVec 256) × (Fin 52 → BitVec 128)) ≃ (Fin 52 → BitVec 256) where
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
      ($ᵗ ((Fin 26 → BitVec 256) × (Fin 52 → BitVec 128)))] =
      𝒮[$ᵗ (Fin 52 → BitVec 256)] :=
  evalSPMF_map_bijective_uniform_cross _ fullTableEquiv fullTableEquiv.bijective

theorem withGhosts_truncate (answers : Fin 26 → BitVec 256)
    (ghosts : Fin 52 → BitVec 128) (chain : Fin 52) :
    (withGhosts answers ghosts chain).extractLsb' 0 128 =
      sourcesFromPairs answers chain := by
  exact BitVec.extractLsb'_append_eq_right

end SigGolfCandidate.Hypertree.GroupedPairedSecrets

end

/-! Lift the paired-source equivalence over all upper graph leaf addresses.
This is the global private-table distribution needed by a grouped graph game. -/

namespace SigGolfCandidate.Hypertree.GroupedGlobalPaired
open SigGolf OracleComp GroupedPairedSecrets

abbrev UpperLeafAddress := Fin 150 × BitVec 160
abbrev PairTable := UpperLeafAddress → Fin 26 → BitVec 256
abbrev SourceTable := UpperLeafAddress → Fin 52 → BitVec 128
abbrev GhostTable := UpperLeafAddress → Fin 52 → BitVec 128
abbrev FullSourceTable := UpperLeafAddress → Fin 52 → BitVec 256

noncomputable instance : SampleableType PairTable := SampleableType.ofFintype PairTable
noncomputable instance : SampleableType SourceTable := SampleableType.ofFintype SourceTable
noncomputable instance : SampleableType FullSourceTable := SampleableType.ofFintype FullSourceTable

def globalSources (answers : PairTable) : SourceTable :=
  fun address => sourcesFromPairs (answers address)

def globalPairs (sources : SourceTable) : PairTable :=
  fun address => pairsFromSources (sources address)

def globalSourceEquiv : PairTable ≃ SourceTable where
  toFun := globalSources
  invFun := globalPairs
  left_inv := by
    intro answers
    funext address
    exact tableEquiv.left_inv (answers address)
  right_inv := by
    intro sources
    funext address
    exact tableEquiv.right_inv (sources address)

theorem uniform_global_sources :
    𝒮[globalSources <$> ($ᵗ PairTable)] = 𝒮[$ᵗ SourceTable] :=
  evalSPMF_map_bijective_uniform_cross PairTable globalSources
    globalSourceEquiv.bijective

theorem source_bind {α : Type} (next : SourceTable → ProbComp α) :
    𝒮[do let answers ← $ᵗ PairTable; next (globalSources answers)] =
      𝒮[do let sources ← $ᵗ SourceTable; next sources] := by
  calc
    _ = 𝒮[do
      let sources ← (do let answers ← $ᵗ PairTable; pure (globalSources answers))
      next sources] := by simp only [bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, ← map_eq_pure_bind, uniform_global_sources,
        ← evalSPMF_bind]

def globalFull (tables : PairTable × GhostTable) : FullSourceTable :=
  fun address => withGhosts (tables.1 address) (tables.2 address)

def globalUnfull (table : FullSourceTable) : PairTable × GhostTable :=
  (fun address => (fullTableEquiv.symm (table address)).1,
    fun address => (fullTableEquiv.symm (table address)).2)

def globalFullEquiv : (PairTable × GhostTable) ≃ FullSourceTable where
  toFun := globalFull
  invFun := globalUnfull
  left_inv := by
    intro tables
    apply Prod.ext
    · funext address
      exact congrArg Prod.fst (fullTableEquiv.left_inv (tables.1 address, tables.2 address))
    · funext address
      exact congrArg Prod.snd (fullTableEquiv.left_inv (tables.1 address, tables.2 address))
  right_inv := by
    intro table
    funext address
    exact fullTableEquiv.right_inv (table address)

theorem uniform_global_full :
    𝒮[globalFull <$> ($ᵗ (PairTable × GhostTable))] =
      𝒮[$ᵗ FullSourceTable] :=
  evalSPMF_map_bijective_uniform_cross _ globalFull globalFullEquiv.bijective

theorem full_bind {α : Type} (next : FullSourceTable → ProbComp α) :
    𝒮[do let tables ← $ᵗ (PairTable × GhostTable); next (globalFull tables)] =
      𝒮[do let sources ← $ᵗ FullSourceTable; next sources] := by
  calc
    _ = 𝒮[do
      let sources ← (do let tables ← $ᵗ (PairTable × GhostTable); pure (globalFull tables))
      next sources] := by simp only [bind_assoc, pure_bind]
    _ = _ := by
      rw [evalSPMF_bind, ← map_eq_pure_bind, uniform_global_full,
        ← evalSPMF_bind]

theorem global_full_truncate (answers : PairTable) (ghosts : GhostTable)
    (address : UpperLeafAddress) (chain : Fin 52) :
    (globalFull (answers, ghosts) address chain).extractLsb' 0 128 =
      globalSources answers address chain :=
  withGhosts_truncate (answers address) (ghosts address) chain

end SigGolfCandidate.Hypertree.GroupedGlobalPaired
