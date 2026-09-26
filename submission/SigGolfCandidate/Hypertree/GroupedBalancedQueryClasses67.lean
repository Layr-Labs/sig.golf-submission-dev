import SigGolfCandidate.Hypertree.GroupedBalancedPrivateGraphDisjoint67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphQuery67
import SigGolfCandidate.Hypertree.SecurityIndexQuery
import SigGolfCandidate.Hypertree.SecuritySharedBudget

/-! The direct67 private-source, public-graph, and H5-index input classes are
pairwise disjoint at the serialized random-oracle query. This is the concrete
input-domain partition behind the shared query budget. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67
open SigGolf SigGolfCandidate.Hypertree OracleSpec Reference
open GroupedBalancedPrivateDerivation67
open GroupedBalancedGraphQuery67
open SecurityGraph
open SecuritySharedBudget
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def SecretKeyEligible (query : Query) : Prop :=
  ∃ secretKey : SecretKey, ∃ slot : Slot,
    GroupedBalancedPrivateDerivation67.input secretKey slot = query

theorem private_input_ne_index (secretKey : SecretKey) (slot : Slot)
    (message : Message) (nonce : Bytes 32) :
    GroupedBalancedPrivateDerivation67.input secretKey slot ≠
      SecurityRandomOracle.indexInput message nonce := by
  intro same
  cases slot with
  | bottom index =>
      have tag := SecurityDomains.addressedInput_tag_eq
        (tag := 1) (tag' := 5) (by
          simpa only [GroupedBalancedPrivateDerivation67.input,
            GroupedBottomIndex.sourceInput, SecurityRandomOracle.indexInput] using same)
      norm_num at tag
  | upper base leaf pair =>
      have tag := SecurityDomains.addressedInput_tag_eq
        (tag := 1) (tag' := 5) (by
          simpa only [GroupedBalancedPrivateDerivation67.input,
            GroupedBalancedAddressDomains67.upperInput,
            SecurityRandomOracle.indexInput] using same)
      norm_num at tag
  | randomizer other =>
      have tag := SecurityDomains.addressedInput_tag_eq
        (tag := 6) (tag' := 5) (by
          simpa only [GroupedBalancedPrivateDerivation67.input,
            SecurityRandomOracle.randomizerInput,
            SecurityRandomOracle.indexInput] using same)
      norm_num at tag

theorem eligible_parse_none (query : Query)
    (eligible : SecretKeyEligible query) :
    SecurityIndexQuery.parse query = none := by
  obtain ⟨secretKey, slot, same⟩ := eligible
  rw [SecurityIndexQuery.parse_none_iff]
  intro message nonce indexEq
  exact private_input_ne_index secretKey slot message nonce
    (same.trans indexEq.symm)

theorem eligible_locate_none (query : Query)
    (eligible : SecretKeyEligible query) : locate query = none := by
  obtain ⟨secretKey, slot, same⟩ := eligible
  unfold locate
  split
  next found =>
    obtain ⟨payload, graphEq⟩ := found.choose_spec
    exact False.elim
      ((GroupedBalancedPrivateGraphDisjoint67.input_ne_public_graph
        secretKey slot found.choose payload) (same.trans graphEq.symm))
  next _ => rfl

theorem parsed_locate_none (query : Query)
    (parsed : (SecurityIndexQuery.parse query).isSome = true) :
    locate query = none := by
  cases parseEq : SecurityIndexQuery.parse query with
  | none => simp [parseEq] at parsed
  | some pair =>
      have inputEq := (SecurityIndexQuery.parse_some_iff query pair).1 parseEq
      rw [← inputEq]
      unfold locate
      split
      next found =>
        obtain ⟨payload, same⟩ := found.choose_spec
        change found.choose.val.input payload =
          (⟨5, 0, 0, 0, 0, 0⟩ : Address).input _ at same
        have tags := congrArg Address.tag (Address.eq_of_input_eq same)
        have tagValue := congrArg (fun tag : Fin 256 => tag.val) tags
        norm_num at tagValue
        rcases found.choose.property with chain | leaf | node <;> omega
      next _ => rfl

theorem located_parse_none (query : Query)
    (located : (locate query).isSome = true) :
    SecurityIndexQuery.parse query = none := by
  cases parseEq : SecurityIndexQuery.parse query with
  | none => rfl
  | some pair =>
      have absent := parsed_locate_none query (by simp [parseEq])
      simp [absent] at located

theorem legacy_eligible_locate_none (query : Query)
    (eligible : SecuritySeparation.SecretKeyEligible query) :
    locate query = none := by
  unfold locate
  split
  next found =>
    obtain ⟨payload, graphEq⟩ := found.choose_spec
    have notChain : found.choose.val.tag.val % 256 ≠ 1 := by
      rcases found.choose.property with chain | leaf | node <;> omega
    have notNonce : found.choose.val.tag.val % 256 ≠ 6 := by
      rcases found.choose.property with chain | leaf | node <;> omega
    have outside := SecurityDomains.not_secretKeyEligible_addressedInput
      found.choose.val.tag.val found.choose.val.level.val
      found.choose.val.tree.toNat found.choose.val.leaf.val
      found.choose.val.chain.val found.choose.val.step.val
      payload notChain notNonce
    change ¬SecuritySeparation.SecretKeyEligible
      (found.choose.input payload) at outside
    rw [graphEq] at outside
    exact False.elim (outside eligible)
  next _ => rfl

theorem legacy_eligible_parse_none (query : Query)
    (eligible : SecuritySeparation.SecretKeyEligible query) :
    SecurityIndexQuery.parse query = none := by
  cases parseEq : SecurityIndexQuery.parse query with
  | none => rfl
  | some pair =>
      exact False.elim
        ((SecurityIndexQuery.parsed_not_secretKeyEligible query pair parseEq)
          eligible)

noncomputable def charge (query : Query) : Counts :=
  { secretKey := if SecuritySeparation.SecretKeyEligible query then 1 else 0
    graph := if (locate query).isSome then 1 else 0
    index := if (SecurityIndexQuery.parse query).isSome then 1 else 0 }

theorem charge_total_le_one (query : Query) :
    (charge query).total ≤ 1 := by
  by_cases secret : SecuritySeparation.SecretKeyEligible query
  · have graph := legacy_eligible_locate_none query secret
    have index := legacy_eligible_parse_none query secret
    simp [charge, Counts.total, secret, graph, index]
  · by_cases graph : (locate query).isSome = true
    · have index := located_parse_none query graph
      simp [charge, Counts.total, secret, graph, index]
    · by_cases index : (SecurityIndexQuery.parse query).isSome = true <;>
        simp [charge, Counts.total, secret, graph, index]

noncomputable def charges : List Query → Counts
  | [] => ⟨0, 0, 0⟩
  | item :: rest =>
      let head := charge item
      let tail := charges rest
      ⟨head.secretKey + tail.secretKey,
        head.graph + tail.graph,
        head.index + tail.index⟩

/-- One physical hash query can enter at most one monitored input class. -/
theorem charges_total_le_length (queries : List Query) :
    (charges queries).total ≤ queries.length := by
  induction queries with
  | nil => simp [charges, Counts.total]
  | cons query rest ih =>
      have one := charge_total_le_one query
      simp only [charges, Counts.total, List.length_cons] at ih one ⊢
      omega

#print axioms private_input_ne_index
#print axioms eligible_locate_none
#print axioms legacy_eligible_locate_none
#print axioms charge_total_le_one
#print axioms charges_total_le_length

end SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67
