import SigGolfCandidate.Hypertree.GroupedHeightThreeUniform

/-!
A height-parametric upper Merkle tree with radix-six WOTS leaves. The tree
address at the root and the leaf address reached by recursion are both placed
in the 192-bit query field. This functional model supports height-three and
height-four groups with one path-correctness proof. `compressions` is a target
for a fused signer that records the selected WOTS prefix while computing the
full endpoint; bytecode refinement remains a separate obligation.
-/

namespace SigGolfCandidate.Hypertree.GroupedUpperTree
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192

abbrev Chain6 := GroupedHeightThreeUniform.Chain6
abbrev digit := GroupedHeightThreeUniform.digit

def secretPair (hash : Hash) (secretKey : SecretKey)
    (base leaf pair : Nat) : BitVec 256 :=
  query hash 1 base leaf 0 pair 0 (bytes secretKey)

def secret (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Chain6) : Digest :=
  let answer := secretPair hash secretKey base leaf (chain.val / 2)
  if chain.val % 2 = 0 then answer.extractLsb' 0 128
    else answer.extractLsb' 128 128

def chainHash (hash : Hash) (base leaf : Nat) (chain : Chain6)
    (step : Nat) (value : Digest) : Digest :=
  truncate (query hash 2 base leaf 0 chain.val step (bytes value))

def endpoint (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Chain6) : Digest :=
  walk (chainHash hash base leaf chain) 0 5
    (secret hash secretKey base leaf chain)

def compressLeaf (hash : Hash) (base leaf : Nat)
    (values : Chain6 → Digest) : Digest :=
  truncate (query hash 3 base leaf 0 0 0 ((List.ofFn values).flatMap bytes))

def leafRoot (hash : Hash) (secretKey : SecretKey) (base leaf : Nat) : Digest :=
  compressLeaf hash base leaf (endpoint hash secretKey base leaf)

def node (hash : Hash) (level address : Nat) (left right : Digest) : Digest :=
  truncate (query hash 4 level address 0 0 0 (bytes left ++ bytes right))

def root (hash : Hash) (secretKey : SecretKey) (base : Nat) :
    Nat → Nat → Digest
  | 0, address => leafRoot hash secretKey base address
  | height + 1, address =>
      node hash (base + height) address
        (root hash secretKey base height (2 * address))
        (root hash secretKey base height (2 * address + 1))

def signValues (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest) : Chain6 → Digest :=
  fun chain => walk (chainHash hash base leaf chain) 0 (digit message chain).val
    (secret hash secretKey base leaf chain)

def recoverLeaf (hash : Hash) (base leaf : Nat) (message : Digest)
    (values : Chain6 → Digest) : Digest :=
  compressLeaf hash base leaf (fun chain =>
    walk (chainHash hash base leaf chain) (digit message chain).val
      (5 - (digit message chain).val) (values chain))

theorem recover_leaf_sign (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest) :
    recoverLeaf hash base leaf message (signValues hash secretKey base leaf message) =
      leafRoot hash secretKey base leaf := by
  simp only [recoverLeaf, signValues, leafRoot]
  congr 1
  funext chain
  have hd : (digit message chain).val ≤ 5 := by
    have := (digit message chain).isLt
    omega
  simpa [endpoint, Nat.add_sub_of_le hd] using
    (walk_append (chainHash hash base leaf chain) 0 (digit message chain).val
      (5 - (digit message chain).val) (secret hash secretKey base leaf chain)).symm

inductive Witness : Nat → Type where
  | leaf (values : Chain6 → Digest) : Witness 0
  | step {height : Nat} (inner : Witness height) (sibling : Digest) :
      Witness (height + 1)

def Witness.encode : {height : Nat} → Witness height → List Byte
  | 0, .leaf values => (List.ofFn values).flatMap bytes
  | _ + 1, .step inner sibling => inner.encode ++ bytes sibling

theorem Witness.encode_length : {height : Nat} → (witness : Witness height) →
    witness.encode.length = (52 + height) * 16
  | 0, .leaf values => by simp [Witness.encode, bytes]
  | height + 1, .step inner sibling => by
      simp only [Witness.encode, List.length_append, Memory.bytes_length]
      rw [Witness.encode_length inner]
      omega

theorem Witness.encode_injective {height : Nat} :
    Function.Injective (Witness.encode : Witness height → List Byte) := by
  intro first second same
  induction first with
  | leaf values =>
      cases second with
      | leaf other =>
          simp only [Witness.encode] at same
          have entries := SignatureEncoding.flatMap_injective (bytes (n := 16)) 16
            (by decide) (fun _ => by simp) (SecurityPacking.bytes_injective 16) same
          have words := List.ofFn_injective entries
          cases words
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

def recover (hash : Hash) (base : Nat) :
    (height address index : Nat) → Digest → Witness height → Digest
  | 0, address, _, message, .leaf values => recoverLeaf hash base address message values
  | height + 1, address, index, message, .step inner sibling =>
      if index / 2 ^ height % 2 = 0 then
        node hash (base + height) address
          (recover hash base height (2 * address) index message inner) sibling
      else
        node hash (base + height) address sibling
          (recover hash base height (2 * address + 1) index message inner)

structure Built (height : Nat) where
  root : Digest
  witness : Witness height
  compressions : Nat

def build (hash : Hash) (secretKey : SecretKey) (base : Nat) :
    (height address index : Nat) → Digest → Built height
  | 0, address, _, message =>
      { root := leafRoot hash secretKey base address,
        witness := .leaf (signValues hash secretKey base address message),
        compressions := 300 }
  | height + 1, address, index, message =>
      if index / 2 ^ height % 2 = 0 then
        let left := build hash secretKey base height (2 * address) index message
        let right := root hash secretKey base height (2 * address + 1)
        { root := node hash (base + height) address left.root right,
          witness := .step left.witness right,
          compressions := left.compressions + (301 * 2 ^ height - 1) + 1 }
      else
        let left := root hash secretKey base height (2 * address)
        let right := build hash secretKey base height (2 * address + 1) index message
        { root := node hash (base + height) address left right.root,
          witness := .step right.witness left,
          compressions := (301 * 2 ^ height - 1) + right.compressions + 1 }

theorem build_root (hash : Hash) (secretKey : SecretKey) (base : Nat)
    (height address index : Nat) (message : Digest) :
    (build hash secretKey base height address index message).root =
      root hash secretKey base height address := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [build, if_pos bit, root]
        rw [ih (2 * address)]
      · simp only [build, if_neg bit, root]
        rw [ih (2 * address + 1)]

theorem recover_build (hash : Hash) (secretKey : SecretKey) (base : Nat)
    (height address index : Nat) (message : Digest) :
    recover hash base height address index message
      (build hash secretKey base height address index message).witness =
      root hash secretKey base height address := by
  induction height generalizing address with
  | zero => exact recover_leaf_sign hash secretKey base address message
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [build, recover, if_pos bit, root]
        rw [ih (2 * address)]
      · simp only [build, recover, if_neg bit, root]
        rw [ih (2 * address + 1)]

theorem build_compressions (hash : Hash) (secretKey : SecretKey) (base : Nat)
    (height address index : Nat) (message : Digest) :
    (build hash secretKey base height address index message).compressions =
      301 * 2 ^ height - 1 := by
  induction height generalizing address with
  | zero => simp [build]
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [build, if_pos bit]
        rw [ih (2 * address), pow_succ]
        have positive : 0 < 2 ^ height := pow_pos (by decide) _
        omega
      · simp only [build, if_neg bit]
        rw [ih (2 * address + 1), pow_succ]
        have positive : 0 < 2 ^ height := pow_pos (by decide) _
        omega

end SigGolfCandidate.Hypertree.GroupedUpperTree
