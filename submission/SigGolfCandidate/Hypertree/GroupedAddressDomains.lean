import SigGolfCandidate.Hypertree.GroupedUpperTree
import SigGolfCandidate.Hypertree.GroupedBottomTree
import SigGolfCandidate.Hypertree.SecurityGraph


/-! The WOTS witness selected in a grouped upper tree belongs to the exact
current index, when the builder is rooted at that index's quotient tree. -/

namespace SigGolfCandidate.Hypertree.GroupedUpperIndex
open SigGolf SigGolfCandidate.Hypertree Reference

def witnessValues : {height : Nat} → GroupedUpperTree.Witness height →
    GroupedUpperTree.Chain6 → Digest
  | 0, .leaf values => values
  | _ + 1, .step inner _ => witnessValues inner

theorem build_witness_values (hash : Hash) (secretKey : SecretKey)
    (base height address index : Nat) (message : Digest) :
    witnessValues (GroupedUpperTree.build hash secretKey base height address index message).witness =
      GroupedUpperTree.signValues hash secretKey base
        (GroupedBottomTree.selectedLeafAddress height address index) message := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [GroupedUpperTree.build, witnessValues,
          GroupedBottomTree.selectedLeafAddress, if_pos bit]
        exact ih (2 * address)
      · simp only [GroupedUpperTree.build, witnessValues,
          GroupedBottomTree.selectedLeafAddress, if_neg bit]
        exact ih (2 * address + 1)

theorem build_witness_values_at_index (hash : Hash) (secretKey : SecretKey)
    (base height index : Nat) (message : Digest) :
    witnessValues
      (GroupedUpperTree.build hash secretKey base height (index / 2 ^ height)
        index message).witness =
      GroupedUpperTree.signValues hash secretKey base index message := by
  rw [build_witness_values, GroupedBottomTree.selectedLeafAddress_index]

end SigGolfCandidate.Hypertree.GroupedUpperIndex


/-! Address separation for the exact bottom source and paired upper sources.
The public query header has byte-sized level and chain fields; all grouped
levels and pair numbers fit without wrapping. -/

namespace SigGolfCandidate.Hypertree.GroupedAddressDomains
open SigGolf SigGolfCandidate.Hypertree Reference SecurityRandomOracle SecurityGraph

def upperInput (secretKey : SecretKey) (base : Fin 160)
    (leaf : BitVec 160) (pair : Fin 26) : Query :=
  addressedInput 1 base.val leaf.toNat 0 pair.val 0 (bytes secretKey)

def upperAddress (base : Fin 160) (leaf : BitVec 160) (pair : Fin 26) : Address :=
  ⟨1, ⟨base.val, by omega⟩, BitVec.ofNat 192 leaf.toNat, 0,
    ⟨pair.val, by omega⟩, 0⟩

theorem upper_address_input (secretKey : SecretKey) (base : Fin 160)
    (leaf : BitVec 160) (pair : Fin 26) :
    (upperAddress base leaf pair).input (bytes secretKey) =
      upperInput secretKey base leaf pair := by
  change addressedInput 1 base.val ((BitVec.ofNat 192 leaf.toNat).toNat) 0
    pair.val 0 (bytes secretKey) =
    addressedInput 1 base.val leaf.toNat 0 pair.val 0 (bytes secretKey)
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field leaf)]

theorem upper_input_fields (secretKey : SecretKey)
    (base base' : Fin 160) (leaf leaf' : BitVec 160) (pair pair' : Fin 26)
    (same : upperInput secretKey base leaf pair =
      upperInput secretKey base' leaf' pair') :
    base = base' ∧ leaf = leaf' ∧ pair = pair' := by
  have addressEq : upperAddress base leaf pair = upperAddress base' leaf' pair' :=
    Address.eq_of_input_eq
      ((upper_address_input secretKey base leaf pair).trans
        (same.trans (upper_address_input secretKey base' leaf' pair').symm))
  have bases := congrArg Address.level addressEq
  have leaves := congrArg Address.tree addressEq
  have pairs := congrArg Address.chain addressEq
  have baseValues := congrArg (fun value : Fin 256 => value.val) bases
  have pairValues := congrArg (fun value : Fin 256 => value.val) pairs
  have baseEq : base = base' := Fin.ext baseValues
  have pairEq : pair = pair' := Fin.ext pairValues
  have leafVals := congrArg BitVec.toNat leaves
  have leafEq : leaf = leaf' := by
    apply BitVec.eq_of_toNat_eq
    change leaf.toNat % 2 ^ 192 = leaf'.toNat % 2 ^ 192 at leafVals
    rw [Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field leaf),
      Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field leaf')] at leafVals
    exact leafVals
  exact ⟨baseEq, leafEq, pairEq⟩

theorem bottom_upper_disjoint (secretKey : SecretKey)
    (index leaf : BitVec 160) (base : Fin 160) (pair : Fin 26)
    (upper : 0 < base.val) :
    GroupedBottomIndex.sourceInput secretKey index ≠
      upperInput secretKey base leaf pair := by
  intro same
  have addressEq : GroupedBottomIndex.sourceAddress index =
      upperAddress base leaf pair :=
    Address.eq_of_input_eq
      ((GroupedBottomIndex.source_address_input secretKey index).trans
        (same.trans (upper_address_input secretKey base leaf pair).symm))
  have levels := congrArg (fun address : Address => address.level.val) addressEq
  simp only [GroupedBottomIndex.sourceAddress, upperAddress] at levels
  omega

theorem upper_pair_query (hash : Hash) (secretKey : SecretKey)
    (base : Fin 160) (leaf : BitVec 160) (pair : Fin 26) :
    GroupedUpperTree.secretPair hash secretKey base.val leaf.toNat pair.val =
      hash (upperInput secretKey base leaf pair) := rfl

end SigGolfCandidate.Hypertree.GroupedAddressDomains
