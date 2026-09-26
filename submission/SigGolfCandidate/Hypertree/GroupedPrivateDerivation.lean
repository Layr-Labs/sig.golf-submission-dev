import SigGolfCandidate.Hypertree.GroupedAddressDomains
import SigGolfCandidate.Hypertree.SecuritySecretKey

/-! Typed private random-oracle slots for the grouped construction. One upper
slot yields the full 256-bit answer used by two adjacent WOTS chain secrets.
All slots map injectively to concrete H inputs, and all carry the whole secret
key at the protected payload position. -/

namespace SigGolfCandidate.Hypertree.GroupedPrivateDerivation
open SigGolf OracleSpec OracleComp SigGolfCandidate.Hypertree Reference
open SecurityRandomOracle SecuritySecretKey GroupedAddressDomains

inductive Slot where
  | bottom (index : BitVec 160)
  | upper (base : Fin 150) (leaf : BitVec 160) (pair : Fin 26)
  | randomizer (message : Message)
  deriving DecidableEq

abbrev SecretSpec : OracleSpec Slot := Slot →ₒ BitVec 256
abbrev SplitWorld := SecretSpec + HashSpec

def baseLevel (base : Fin 150) : Fin 160 := ⟨base.val + 10, by omega⟩

theorem baseLevel_injective : Function.Injective baseLevel := by
  intro first second same
  have values := congrArg (fun level : Fin 160 => level.val) same
  exact Fin.ext (by simpa only [baseLevel] using Nat.add_right_cancel values)

def input (secretKey : SecretKey) : Slot → Query
  | .bottom index => GroupedBottomIndex.sourceInput secretKey index
  | .upper base leaf pair => upperInput secretKey (baseLevel base) leaf pair
  | .randomizer message => randomizerInput secretKey message

@[simp] theorem bottom_input_length (secretKey : SecretKey) (index : BitVec 160) :
    (input secretKey (.bottom index)).1 = 512 := by
  simp [input, GroupedBottomIndex.sourceInput, bytes]

@[simp] theorem upper_input_length (secretKey : SecretKey) (base : Fin 150)
    (leaf : BitVec 160) (pair : Fin 26) :
    (input secretKey (.upper base leaf pair)).1 = 512 := by
  simp [input, upperInput, bytes]

@[simp] theorem randomizer_input_length (secretKey : SecretKey) (message : Message) :
    (input secretKey (.randomizer message)).1 = 768 := by
  simp [input]

theorem input_injective (secretKey : SecretKey) : Function.Injective (input secretKey) := by
  intro first second same
  cases first with
  | bottom index =>
      cases second with
      | bottom other =>
          exact congrArg Slot.bottom
            (GroupedBottomIndex.sourceInput_injective secretKey same)
      | upper base leaf pair =>
          exact False.elim ((bottom_upper_disjoint secretKey index leaf
            (baseLevel base) pair (by simp [baseLevel])) same)
      | randomizer message =>
          have lengths := congrArg Sigma.fst same
          simp only [bottom_input_length, randomizer_input_length] at lengths
          omega
  | upper base leaf pair =>
      cases second with
      | bottom index =>
          exact False.elim ((bottom_upper_disjoint secretKey index leaf
            (baseLevel base) pair (by simp [baseLevel])) same.symm)
      | upper otherBase otherLeaf otherPair =>
          obtain ⟨levels, leaves, pairs⟩ := upper_input_fields secretKey
            (baseLevel base) (baseLevel otherBase) leaf otherLeaf pair otherPair same
          have bases := baseLevel_injective levels
          cases bases
          cases leaves
          cases pairs
          rfl
      | randomizer message =>
          have lengths := congrArg Sigma.fst same
          simp only [upper_input_length, randomizer_input_length] at lengths
          omega
  | randomizer message =>
      cases second with
      | bottom index =>
          have lengths := congrArg Sigma.fst same
          simp only [bottom_input_length, randomizer_input_length] at lengths
          omega
      | upper base leaf pair =>
          have lengths := congrArg Sigma.fst same
          simp only [upper_input_length, randomizer_input_length] at lengths
          omega
      | randomizer other =>
          have old : SecurityDerivation.input secretKey
              (.randomizer message) =
              SecurityDerivation.input secretKey (.randomizer other) := same
          have equal := SecurityDerivation.input_injective secretKey old
          cases equal
          rfl

theorem input_secretKeyAt (secretKey : SecretKey) (slot : Slot) :
    SecretKeyAt (input secretKey slot) secretKey := by
  cases slot with
  | bottom index =>
      exact secretKeyAt_secret secretKey 0 index.toNat 0 0
  | upper base leaf pair =>
      exact secretKeyAt_secret secretKey (baseLevel base).val leaf.toNat 0 pair.val
  | randomizer message =>
      exact secretKeyAt_randomizer secretKey message

theorem secretKeyed_input_injective :
    Function.Injective (fun pair : SecretKey × Slot => input pair.1 pair.2) := by
  intro first second same
  change input first.1 first.2 = input second.1 second.2 at same
  have atFirst : SecretKeyAt (input second.1 second.2) first.1 := by
    rw [← same]
    exact input_secretKeyAt first.1 first.2
  have keys : first.1 = second.1 :=
    secretKeyAt_unique atFirst (input_secretKeyAt second.1 second.2)
  apply Prod.ext keys
  apply input_injective second.1
  simpa [keys] using same

def realDerivation (secretKey : SecretKey) :
    QueryImpl SecretSpec (OracleComp HashSpec) :=
  fun slot => liftM (HashSpec.query (input secretKey slot))

def realImplementation (secretKey : SecretKey) :
    QueryImpl SplitWorld (OracleComp HashSpec) :=
  realDerivation secretKey +
    (HasQuery.toQueryImpl (spec := HashSpec) (m := OracleComp HashSpec))

theorem eval_real_bottom (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) :
    truncate (evalWithAnswerFn hash (realDerivation secretKey (.bottom index))) =
      GroupedBottomTree.secret hash secretKey index.toNat := rfl

theorem eval_real_upper (hash : Hash) (secretKey : SecretKey)
    (base : Fin 150) (leaf : BitVec 160) (pair : Fin 26) :
    evalWithAnswerFn hash (realDerivation secretKey (.upper base leaf pair)) =
      GroupedUpperTree.secretPair hash secretKey (base.val + 10) leaf.toNat pair.val := rfl

theorem eval_real_randomizer (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    evalWithAnswerFn hash (realDerivation secretKey (.randomizer message)) =
      Reference.randomizer hash secretKey message := rfl

end SigGolfCandidate.Hypertree.GroupedPrivateDerivation
