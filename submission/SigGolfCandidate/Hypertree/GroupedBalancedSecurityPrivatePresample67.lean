import SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraphPresample67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateFactors67

/-! Eager sampling of the direct67 private derivation inputs, retaining their
exact locations in the shared lazy random-oracle cache. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityPrivatePresample67
open SigGolf OracleComp OracleSpec Reference SecurityCache
open GroupedBalancedPrivateDerivation67 GroupedBalancedPrivateFactors67
open scoped Classical

def populate (secretKey : SecretKey) : List Slot → PrivateTable →
    QueryCache HashSpec → QueryCache HashSpec
  | [], _, cache => cache
  | slot :: rest, answers, cache =>
      populate secretKey rest answers
        (cache.cacheQuery (input secretKey slot) (answers slot))

theorem populate_update_of_not_mem (secretKey : SecretKey)
    (slots : List Slot) (slot : Slot) (absent : slot ∉ slots)
    (answers : PrivateTable) (value : BitVec 256)
    (cache : QueryCache HashSpec) :
    populate secretKey slots (Function.update answers slot value) cache =
      populate secretKey slots answers cache := by
  induction slots generalizing cache with
  | nil => rfl
  | cons first rest ih =>
      have different : first ≠ slot := by
        intro same
        exact absent (by simp [same])
      have restAbsent : slot ∉ rest :=
        fun member => absent (List.mem_cons_of_mem _ member)
      simp only [populate, Function.update_of_ne different]
      exact ih restAbsent _

theorem populate_other (secretKey : SecretKey) (slots : List Slot)
    (answers : PrivateTable) (cache : QueryCache HashSpec) (query : Query)
    (outside : ∀ slot ∈ slots, query ≠ input secretKey slot) :
    populate secretKey slots answers cache query = cache query := by
  induction slots generalizing cache with
  | nil => rfl
  | cons first rest ih =>
      rw [populate, ih]
      · exact QueryCache.cacheQuery_of_ne _ _ (outside first (by simp))
      · intro slot member
        exact outside slot (List.mem_cons_of_mem _ member)

theorem populate_lookup (secretKey : SecretKey) (slots : List Slot)
    (distinct : slots.Nodup) (answers : PrivateTable)
    (cache : QueryCache HashSpec) (slot : Slot) (member : slot ∈ slots) :
    populate secretKey slots answers cache (input secretKey slot) =
      some (answers slot) := by
  induction slots generalizing cache with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
      by_cases same : slot = first
      · subst slot
        rw [populate, populate_other]
        · exact QueryCache.cacheQuery_self _ _ _
        · intro other otherMember
          exact fun queryEq => notRest
            ((input_injective secretKey queryEq).symm ▸ otherMember)
      · have restMember : slot ∈ rest := by simpa [same] using member
        exact ih restDistinct _ restMember

theorem uniform_update_bind {α : Type} (slot : Slot)
    (next : PrivateTable → ProbComp α) :
    𝒮[do
      let value ← $ᵗ BitVec 256
      let answers ← $ᵗ PrivateTable
      next (Function.update answers slot value)] =
      𝒮[do let answers ← $ᵗ PrivateTable; next answers] := by
  calc
    _ = 𝒮[do
      let updated ← (do
        let value ← $ᵗ BitVec 256
        let answers ← $ᵗ PrivateTable
        pure (Function.update answers slot value))
      next updated] := by simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalSPMF_bind, evalSPMF_uniformSample_bind_update, evalSPMF_bind]

/-- Uniform private answers can be embedded at any pairwise distinct direct67
private H inputs without changing the distribution of an arbitrary observable
continuation. All continuation counters remain in the result. -/
theorem populate_presampling {α : Type} (secretKey : SecretKey)
    (slots : List Slot) (distinct : slots.Nodup)
    (program : OracleComp World α) (cache : QueryCache HashSpec)
    (fresh : ∀ slot ∈ slots, cache (input secretKey slot) = none) :
    𝒮[do
      let answers ← $ᵗ PrivateTable
      SecurityGraphHidden.observe program
        (populate secretKey slots answers cache)] =
      𝒮[SecurityGraphHidden.observe program cache] := by
  induction slots generalizing cache with
  | nil =>
      simp only [populate]
      apply evalSPMF_ext
      intro output
      rw [probOutput_bind_const]
      simp
  | cons first rest ih =>
      obtain ⟨notRest, restDistinct⟩ := List.nodup_cons.mp distinct
      have restFresh (value : BitVec 256) :
          ∀ slot ∈ rest,
            (cache.cacheQuery (input secretKey first) value)
              (input secretKey slot) = none := by
        intro slot member
        have different : input secretKey slot ≠ input secretKey first :=
          fun same => notRest ((input_injective secretKey same).symm ▸ member)
        rw [QueryCache.cacheQuery_of_ne _ _ different]
        exact fresh slot (List.mem_cons_of_mem _ member)
      calc
        _ = 𝒮[do
          let value ← $ᵗ BitVec 256
          let answers ← $ᵗ PrivateTable
          SecurityGraphHidden.observe program
            (populate secretKey rest answers
              (cache.cacheQuery (input secretKey first) value))] := by
            rw [← uniform_update_bind first (fun answers =>
              SecurityGraphHidden.observe program
                (populate secretKey (first :: rest) answers cache))]
            apply evalSPMF_bind_congr
            intro value _
            apply evalSPMF_bind_congr
            intro answers _
            simp only [populate, Function.update_self]
            rw [populate_update_of_not_mem secretKey rest first notRest]
        _ = 𝒮[do
          let value ← $ᵗ BitVec 256
          SecurityGraphHidden.observe program
            (cache.cacheQuery (input secretKey first) value)] := by
            apply evalSPMF_bind_congr
            intro value _
            exact ih restDistinct
              (cache.cacheQuery (input secretKey first) value)
              (restFresh value)
        _ = _ := SecurityGraphHidden.fill_fresh program cache
          (input secretKey first) (fresh first (by simp))

#print axioms populate_presampling

noncomputable def allSlots : List Slot := Finset.univ.toList

theorem allSlots_nodup : allSlots.Nodup := Finset.nodup_toList _

theorem allSlots_complete (slot : Slot) : slot ∈ allSlots := by
  simp [allSlots]

/-- An eager independent uniform table at every direct67 private input has
exactly the same observable law as the originally empty lazy oracle. -/
theorem all_private_presampling {α : Type} (secretKey : SecretKey)
    (program : OracleComp World α) :
    𝒮[SecurityGraphHidden.observe program ∅] =
      𝒮[do
        let answers ← $ᵗ PrivateTable
        SecurityGraphHidden.observe program
          (populate secretKey allSlots answers ∅)] := by
  exact (populate_presampling secretKey allSlots allSlots_nodup
    program ∅ (by intros; rfl)).symm

theorem all_private_lookup (secretKey : SecretKey)
    (answers : PrivateTable) (slot : Slot) :
    populate secretKey allSlots answers ∅ (input secretKey slot) =
      some (answers slot) :=
  populate_lookup secretKey allSlots allSlots_nodup answers ∅ slot
    (allSlots_complete slot)

theorem all_private_other (secretKey : SecretKey)
    (answers : PrivateTable) (query : Query)
    (outside : ∀ slot : Slot, query ≠ input secretKey slot) :
    populate secretKey allSlots answers ∅ query = none := by
  rw [populate_other secretKey allSlots answers ∅ query
    (fun slot _ => outside slot)]
  rfl

#print axioms all_private_presampling
#print axioms all_private_lookup
#print axioms all_private_other

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityPrivatePresample67
