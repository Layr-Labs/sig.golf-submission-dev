import SigGolfCandidate.Hypertree.GroupedHeightThreeUniform
import SigGolfCandidate.Hypertree.SecurityGraph

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBottomIndex; its only importer was SigGolfCandidate.Hypertree.GroupedBottomTree. -/
section
/-! The bottom source address in the grouped tree retains all 160 index bits.
This is the address property needed to count a fresh bottom seed as an unopened
source, even after many signatures disclose seeds at other indices. -/

namespace SigGolfCandidate.Hypertree.GroupedBottomIndex
open SigGolf SigGolfCandidate.Hypertree
open Reference SecurityPacking SecurityRandomOracle SecurityGraph GroupedHeightThreeUniform

def treeOf (index : BitVec 160) : Nat := index.toNat / 16
def childOf (index : BitVec 160) : Nat := index.toNat % 16

theorem index_recompose (index : BitVec 160) :
    16 * treeOf index + childOf index = index.toNat := by
  unfold treeOf childOf
  omega

theorem tree_bounded (index : BitVec 160) : treeOf index < 2 ^ 156 := by
  unfold treeOf
  have h := index.isLt
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  have pow : 2 ^ 156 * 16 = 2 ^ 160 := by decide
  omega

theorem index_fits_tree_field (index : BitVec 160) : index.toNat < 2 ^ 192 :=
  lt_of_lt_of_le index.isLt (by decide)

def sourceInput (secretKey : SecretKey) (index : BitVec 160) : Query :=
  addressedInput 1 0 index.toNat 0 0 0 (bytes secretKey)

def sourceAddress (index : BitVec 160) : Address :=
  ⟨1, 0, BitVec.ofNat 192 index.toNat, 0, 0, 0⟩

theorem source_address_input (secretKey : SecretKey) (index : BitVec 160) :
    (sourceAddress index).input (bytes secretKey) = sourceInput secretKey index := by
  change addressedInput 1 0 ((BitVec.ofNat 192 index.toNat).toNat) 0 0 0
    (bytes secretKey) = addressedInput 1 0 index.toNat 0 0 0 (bytes secretKey)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (index_fits_tree_field index)]

theorem sourceInput_injective (secretKey : SecretKey) :
    Function.Injective (sourceInput secretKey) := by
  intro x y same
  have same' : (sourceAddress x).input (bytes secretKey) =
      (sourceAddress y).input (bytes secretKey) :=
    (source_address_input secretKey x).trans
      (same.trans (source_address_input secretKey y).symm)
  have addresses : sourceAddress x = sourceAddress y := Address.eq_of_input_eq same'
  have trees := congrArg Address.tree addresses
  have values := congrArg BitVec.toNat trees
  apply BitVec.eq_of_toNat_eq
  change x.toNat % 2 ^ 192 = y.toNat % 2 ^ 192 at values
  rw [Nat.mod_eq_of_lt (index_fits_tree_field x),
    Nat.mod_eq_of_lt (index_fits_tree_field y)] at values
  exact values

theorem bottom_secret_query (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) :
    GroupedHeightThreeUniform.bottomSecret hash secretKey
      (treeOf index) (childOf index) = truncate (hash (sourceInput secretKey index)) := by
  simp only [GroupedHeightThreeUniform.bottomSecret]
  rw [index_recompose]
  rfl

theorem sourceInput_fresh (secretKey : SecretKey) (signed : Finset (BitVec 160))
    (index : BitVec 160) (fresh : index ∉ signed) :
    ∀ other ∈ signed, sourceInput secretKey index ≠ sourceInput secretKey other := by
  intro other member same
  exact fresh ((sourceInput_injective secretKey same) ▸ member)

end SigGolfCandidate.Hypertree.GroupedBottomIndex

end

/-! A height-parametric, tree-addressed bottom preimage Merkle tree.
The builder visits each leaf and internal node exactly once, producing the
canonical root and an authentication witness for one selected full index. -/

namespace SigGolfCandidate.Hypertree.GroupedBottomTree
open SigGolf SigGolfCandidate.Hypertree Reference SecurityRandomOracle

def secret (hash : Hash) (secretKey : SecretKey) (leaf : Nat) : Digest :=
  truncate (query hash 1 0 leaf 0 0 0 (bytes secretKey))

def leafFromSeed (hash : Hash) (leaf : Nat) (seed : Digest) : Digest :=
  truncate (query hash 2 0 leaf 0 0 0 (bytes seed))

def leafRoot (hash : Hash) (secretKey : SecretKey) (leaf : Nat) : Digest :=
  leafFromSeed hash leaf (secret hash secretKey leaf)

def node (hash : Hash) (level address : Nat) (left right : Digest) : Digest :=
  truncate (query hash 4 level address 0 0 0 (bytes left ++ bytes right))

theorem secret_query_compressions (secretKey : SecretKey) (leaf : Nat) :
    compressions (addressedInput 1 0 leaf 0 0 0 (bytes secretKey)).1 = 1 := by
  simp only [addressedInput, Reference.packed, List.length_append, Memory.bytes_length]
  decide

theorem leaf_query_compressions (leaf : Nat) (seed : Digest) :
    compressions (addressedInput 2 0 leaf 0 0 0 (bytes seed)).1 = 1 := by
  simp only [addressedInput, Reference.packed, List.length_append, Memory.bytes_length]
  decide

theorem node_query_compressions (level address : Nat) (left right : Digest) :
    compressions (addressedInput 4 level address 0 0 0 (bytes left ++ bytes right)).1 = 1 := by
  simp only [addressedInput, Reference.packed, List.length_append, Memory.bytes_length]
  decide

def root (hash : Hash) (secretKey : SecretKey) : Nat → Nat → Digest
  | 0, address => leafRoot hash secretKey address
  | height + 1, address =>
      node hash height address
        (root hash secretKey height (2 * address))
        (root hash secretKey height (2 * address + 1))

inductive Witness : Nat → Type where
  | seed (value : Digest) : Witness 0
  | step {height : Nat} (inner : Witness height) (sibling : Digest) :
      Witness (height + 1)

def Witness.seedValue : {height : Nat} → Witness height → Digest
  | 0, .seed value => value
  | _ + 1, .step inner _ => inner.seedValue

def Witness.encode : {height : Nat} → Witness height → List Byte
  | 0, .seed value => bytes value
  | _ + 1, .step inner sibling => inner.encode ++ bytes sibling

theorem Witness.encode_length : {height : Nat} → (witness : Witness height) →
    witness.encode.length = (height + 1) * 16
  | 0, .seed value => by simp [Witness.encode, bytes]
  | height + 1, .step inner sibling => by
      simp only [Witness.encode, List.length_append, Memory.bytes_length]
      rw [Witness.encode_length inner]
      omega

theorem Witness.encode_injective {height : Nat} :
    Function.Injective (Witness.encode : Witness height → List Byte) := by
  intro first second same
  induction first with
  | seed value =>
      cases second with
      | seed other =>
          have values := SecurityPacking.bytes_injective 16 same
          cases values
          rfl
  | @step h inner sibling ih =>
      cases second with
      | step other otherSibling =>
          simp only [Witness.encode] at same
          have lengths : inner.encode.length = other.encode.length := by
            rw [Witness.encode_length inner, Witness.encode_length other]
          have innerBytes := List.append_inj_left same lengths
          have siblingBytes := List.append_inj_right same lengths
          have innerEq := ih innerBytes
          have siblingEq := SecurityPacking.bytes_injective 16 siblingBytes
          cases innerEq
          cases siblingEq
          rfl

def recover (hash : Hash) : (height address index : Nat) → Witness height → Digest
  | 0, address, _, .seed seed => leafFromSeed hash address seed
  | height + 1, address, index, .step inner sibling =>
      if index / 2 ^ height % 2 = 0 then
        node hash height address
          (recover hash height (2 * address) index inner) sibling
      else
        node hash height address sibling
          (recover hash height (2 * address + 1) index inner)

structure Built (height : Nat) where
  root : Digest
  witness : Witness height
  compressions : Nat

def build (hash : Hash) (secretKey : SecretKey) :
    (height address index : Nat) → Built height
  | 0, address, _ =>
      let seed := secret hash secretKey address
      { root := leafFromSeed hash address seed,
        witness := .seed seed,
        compressions := 2 }
  | height + 1, address, index =>
      let left := build hash secretKey height (2 * address) index
      let right := build hash secretKey height (2 * address + 1) index
      { root := node hash height address left.root right.root,
        witness := if index / 2 ^ height % 2 = 0 then
          .step left.witness right.root else .step right.witness left.root,
        compressions := left.compressions + right.compressions + 1 }

def selectedLeafAddress : (height address index : Nat) → Nat
  | 0, address, _ => address
  | height + 1, address, index =>
      if index / 2 ^ height % 2 = 0 then
        selectedLeafAddress height (2 * address) index
      else
        selectedLeafAddress height (2 * address + 1) index

theorem build_seed (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) :
    (build hash secretKey height address index).witness.seedValue =
      secret hash secretKey (selectedLeafAddress height address index) := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [build, Witness.seedValue, selectedLeafAddress, if_pos bit]
        exact ih (2 * address)
      · simp only [build, Witness.seedValue, selectedLeafAddress, if_neg bit]
        exact ih (2 * address + 1)

private theorem child_address (height index : Nat) :
    (if index / 2 ^ height % 2 = 0 then 2 * (index / 2 ^ (height + 1))
      else 2 * (index / 2 ^ (height + 1)) + 1) = index / 2 ^ height := by
  have quotient : (index / 2 ^ height) / 2 = index / 2 ^ (height + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have remainder := Nat.mod_add_div (index / 2 ^ height) 2
  have small := Nat.mod_lt (index / 2 ^ height) (by decide : 0 < 2)
  by_cases bit : index / 2 ^ height % 2 = 0
  · simp only [if_pos bit]
    omega
  · simp only [if_neg bit]
    omega

theorem selectedLeafAddress_index (height index : Nat) :
    selectedLeafAddress height (index / 2 ^ height) index = index := by
  induction height with
  | zero => simp [selectedLeafAddress]
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [selectedLeafAddress, if_pos bit]
        have address_eq : 2 * (index / 2 ^ (height + 1)) = index / 2 ^ height := by
          simpa only [if_pos bit] using child_address height index
        rw [address_eq]
        exact ih
      · simp only [selectedLeafAddress, if_neg bit]
        have address_eq : 2 * (index / 2 ^ (height + 1)) + 1 = index / 2 ^ height := by
          simpa only [if_neg bit] using child_address height index
        rw [address_eq]
        exact ih

theorem build_seed_at_full_index (hash : Hash) (secretKey : SecretKey)
    (height index : Nat) :
    (build hash secretKey height (index / 2 ^ height) index).witness.seedValue =
      secret hash secretKey index := by
  rw [build_seed, selectedLeafAddress_index]

theorem height_ten_seed_query (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) :
    (build hash secretKey 10 (index.toNat / 2 ^ 10) index.toNat).witness.seedValue =
      truncate (hash (GroupedBottomIndex.sourceInput secretKey index)) := by
  rw [build_seed_at_full_index]
  rfl

theorem build_root (hash : Hash) (secretKey : SecretKey) (height address index : Nat) :
    (build hash secretKey height address index).root = root hash secretKey height address := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      simp only [build, root]
      rw [ih (2 * address), ih (2 * address + 1)]

theorem recover_build (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) :
    recover hash height address index
      (build hash secretKey height address index).witness =
      root hash secretKey height address := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [build, recover, if_pos bit, root]
        rw [ih (2 * address), build_root hash secretKey height (2 * address + 1) index]
      · simp only [build, recover, if_neg bit, root]
        rw [build_root hash secretKey height (2 * address) index,
          ih (2 * address + 1)]

theorem build_compressions (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) :
    (build hash secretKey height address index).compressions = 3 * 2 ^ height - 1 := by
  induction height generalizing address with
  | zero => simp [build]
  | succ height ih =>
      simp only [build]
      rw [ih (2 * address), ih (2 * address + 1), pow_succ]
      have positive : 0 < 2 ^ height := pow_pos (by decide) _
      omega

theorem build_witness_bytes (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) :
    ((build hash secretKey height address index).witness.encode).length =
      (height + 1) * 16 := Witness.encode_length _

theorem height_ten (hash : Hash) (secretKey : SecretKey) (address index : Nat) :
    (build hash secretKey 10 address index).compressions = 3071 ∧
    ((build hash secretKey 10 address index).witness.encode).length = 176 ∧
    recover hash 10 address index
      (build hash secretKey 10 address index).witness =
      root hash secretKey 10 address := by
  exact ⟨by simpa using build_compressions hash secretKey 10 address index,
    by simpa using build_witness_bytes hash secretKey 10 address index,
    recover_build hash secretKey 10 address index⟩

end SigGolfCandidate.Hypertree.GroupedBottomTree
