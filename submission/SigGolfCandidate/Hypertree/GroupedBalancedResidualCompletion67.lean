import SigGolfCandidate.Hypertree.GroupedBalancedVerifierForgeryElim67
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateLegacyEligible67

/-! Complete a final lazy public cache to a total hash while assigning exact
direct67 bottom, paired upper, and randomizer private outputs. The only
required freshness condition is absence of cached inputs from the private
address range for the sampled secret key. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedResidualCompletion67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorTable67
open GroupedBalancedPrivateDerivation67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
open scoped Classical

def privateValue (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable) :
    GroupedBalancedPrivateDerivation67.Slot → BitVec 256
  | .bottom index => table (.inr (.inl index))
  | .upper base leaf pair => (privateOf table).upper base leaf pair
  | .randomizer message => answers (.randomizer message)

noncomputable def completion (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec) : Hash :=
  fun query =>
    if found : ∃ slot : GroupedBalancedPrivateDerivation67.Slot,
        GroupedBalancedPrivateDerivation67.input secretKey slot = query
    then privateValue table answers found.choose
    else (cache query).getD 0

theorem completion_private (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (slot : GroupedBalancedPrivateDerivation67.Slot) :
    completion table answers secretKey cache
      (GroupedBalancedPrivateDerivation67.input secretKey slot) =
      privateValue table answers slot := by
  unfold completion
  have found : ∃ other : GroupedBalancedPrivateDerivation67.Slot,
      GroupedBalancedPrivateDerivation67.input secretKey other =
        GroupedBalancedPrivateDerivation67.input secretKey slot :=
    ⟨slot, rfl⟩
  rw [dif_pos found]
  have same := GroupedBalancedPrivateDerivation67.input_injective secretKey
    found.choose_spec
  rw [same]

theorem completion_agrees (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (privateFresh : ∀ slot : GroupedBalancedPrivateDerivation67.Slot,
      cache (GroupedBalancedPrivateDerivation67.input secretKey slot) = none) :
    cache.AgreesWithFn (completion table answers secretKey cache) := by
  intro query value present
  unfold completion
  by_cases found : ∃ slot : GroupedBalancedPrivateDerivation67.Slot,
      GroupedBalancedPrivateDerivation67.input secretKey slot = query
  · have absent := privateFresh found.choose
    rw [found.choose_spec] at absent
    rw [absent] at present
    cases present
  · rw [dif_neg found, present]
    rfl

theorem completion_bottom (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (index : BitVec 160) :
    (GroupedBalancedGraphReference67.sourceAnswers
      (completion table answers secretKey cache) secretKey).bottom index =
    (privateOf table).bottom index := by
  simpa only [GroupedBalancedGraphReference67.sourceAnswers,
    GroupedBalancedPrivateDerivation67.input, privateValue,
    GroupedBalancedGraphMonitorTable67.bottom_source] using
    completion_private table answers secretKey cache (.bottom index)

theorem completion_upper (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedGraphPayload67.chainSource
      (GroupedBalancedGraphReference67.sourceAnswers
        (completion table answers secretKey cache) secretKey)
      base leaf chain =
    GroupedBalancedGraphPayload67.chainSource
      (privateOf table) base leaf chain := by
  have upperEq :
      (GroupedBalancedGraphReference67.sourceAnswers
        (completion table answers secretKey cache) secretKey).upper =
      (privateOf table).upper := by
    funext otherBase otherLeaf pair
    simpa only [GroupedBalancedGraphReference67.sourceAnswers,
      GroupedBalancedPrivateDerivation67.input, privateValue,
      GroupedBalancedPrivateDerivation67.baseLevel,
      GroupedBalancedAddressDomains67.upperInput] using
      completion_private table answers secretKey cache
        (.upper otherBase otherLeaf pair)
  exact congrArg (fun upper =>
    GroupedBalancedGraphPayload67.chainSource
      ⟨(privateOf table).bottom, upper⟩ base leaf chain) upperEq

theorem completion_randomizer (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (message : Message) :
    Reference.randomizer (completion table answers secretKey cache)
      secretKey message = answers (.randomizer message) := by
  change completion table answers secretKey cache
      (SecurityRandomOracle.randomizerInput secretKey message) =
    answers (.randomizer message)
  exact completion_private table answers secretKey cache
    (.randomizer message)

#print axioms completion_private
#print axioms completion_agrees
#print axioms completion_bottom
#print axioms completion_upper
#print axioms completion_randomizer

end SigGolfCandidate.Hypertree.GroupedBalancedResidualCompletion67
