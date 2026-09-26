import SigGolfCandidate.Hypertree.Signature

/-!
An isolated, functional prototype for a 160-bit hypertree with a four-bit
bottom tree and 52 three-bit upper trees. This file does not alter the active
submission. Every upper tree has eight WOTS leaves, one selected fragment,
and three 16-byte authentication siblings. Its base-four WOTS uses 64 message
digits and four checksum digits.

The bottom tree in this prototype has no high-index tree address. Functional
correctness alone does not establish the required unforgeability: after bottom
seeds are exposed, an upper-index match can reuse a signed upper path. The
tree-addressed bottom construction in `GroupedHeightThreeUniform` fixes this
issue for the radix-six prototype.
-/

namespace SigGolfCandidate.Hypertree.GroupedHeightThree
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192

abbrev Chain4 := Fin 68

def messageDigit (message : Digest) (i : Fin 64) : Nat :=
  message.toNat / 4 ^ i.val % 4

def checksum (message : Digest) : Nat :=
  192 - ∑ i : Fin 64, messageDigit message i

def digit (message : Digest) (chain : Chain4) : Fin 4 :=
  ⟨(if chain.val < 64 then message.toNat / 4 ^ chain.val
    else checksum message / 4 ^ (chain.val - 64)) % 4,
    Nat.mod_lt _ (by decide)⟩

def base (group : Nat) : Nat := 4 + 3 * group

def leafAddress (tree child : Nat) : Nat := 8 * tree + child

def secret (hash : Hash) (secretKey : SecretKey) (group tree child : Nat)
    (chain : Chain4) : Digest :=
  truncate (query hash 1 (base group) (leafAddress tree child) 0 chain.val 0 (bytes secretKey))

def chainHash (hash : Hash) (group tree child : Nat) (chain : Chain4)
    (step : Nat) (value : Digest) : Digest :=
  truncate (query hash 2 (base group) (leafAddress tree child) 0 chain.val step (bytes value))

def endpoint (hash : Hash) (secretKey : SecretKey) (group tree child : Nat)
    (chain : Chain4) : Digest :=
  walk (chainHash hash group tree child chain) 0 3 (secret hash secretKey group tree child chain)

def compressLeaf (hash : Hash) (group tree child : Nat)
    (values : Chain4 → Digest) : Digest :=
  truncate (query hash 3 (base group) (leafAddress tree child) 0 0 0
    ((List.ofFn values).flatMap bytes))

def leafRoot (hash : Hash) (secretKey : SecretKey) (group tree child : Nat) : Digest :=
  compressLeaf hash group tree child (endpoint hash secretKey group tree child)

def node (hash : Hash) (level tree : Nat) (left right : Digest) : Digest :=
  truncate (query hash 4 level tree 0 0 0 (bytes left ++ bytes right))

def pair (hash : Hash) (secretKey : SecretKey) (group tree pairIndex : Nat) : Digest :=
  node hash (base group) (4 * tree + pairIndex)
    (leafRoot hash secretKey group tree (2 * pairIndex))
    (leafRoot hash secretKey group tree (2 * pairIndex + 1))

def quad (hash : Hash) (secretKey : SecretKey) (group tree quadIndex : Nat) : Digest :=
  node hash (base group + 1) (2 * tree + quadIndex)
    (pair hash secretKey group tree (2 * quadIndex))
    (pair hash secretKey group tree (2 * quadIndex + 1))

def root (hash : Hash) (secretKey : SecretKey) (group tree : Nat) : Digest :=
  node hash (base group + 2) tree
    (quad hash secretKey group tree 0) (quad hash secretKey group tree 1)

structure UpperSignature where
  values : Chain4 → Digest
  sibling0 : Digest
  sibling1 : Digest
  sibling2 : Digest

def signUpper (hash : Hash) (secretKey : SecretKey) (group tree : Nat)
    (child : Fin 8) (message : Digest) : UpperSignature where
  values := fun chain => walk (chainHash hash group tree child.val chain) 0
    (digit message chain).val (secret hash secretKey group tree child.val chain)
  sibling0 := leafRoot hash secretKey group tree (if child.val % 2 = 0 then child.val + 1 else child.val - 1)
  sibling1 := pair hash secretKey group tree
    (if child.val / 2 % 2 = 0 then child.val / 2 + 1 else child.val / 2 - 1)
  sibling2 := quad hash secretKey group tree (if child.val / 4 = 0 then 1 else 0)

def recoverLeaf (hash : Hash) (group tree child : Nat) (message : Digest)
    (signature : UpperSignature) : Digest :=
  compressLeaf hash group tree child (fun chain =>
    walk (chainHash hash group tree child chain) (digit message chain).val
      (3 - (digit message chain).val) (signature.values chain))

def recoverUpper (hash : Hash) (group tree : Nat) (child : Fin 8)
    (message : Digest) (signature : UpperSignature) : Digest :=
  let leaf := recoverLeaf hash group tree child.val message signature
  let first := if child.val % 2 = 0 then
    node hash (base group) (4 * tree + child.val / 2) leaf signature.sibling0
    else node hash (base group) (4 * tree + child.val / 2) signature.sibling0 leaf
  let second := if child.val / 2 % 2 = 0 then
    node hash (base group + 1) (2 * tree + child.val / 4) first signature.sibling1
    else node hash (base group + 1) (2 * tree + child.val / 4) signature.sibling1 first
  if child.val / 4 = 0 then node hash (base group + 2) tree second signature.sibling2
    else node hash (base group + 2) tree signature.sibling2 second

theorem recover_leaf_sign (hash : Hash) (secretKey : SecretKey) (group tree : Nat)
    (child : Fin 8) (message : Digest) :
    recoverLeaf hash group tree child.val message (signUpper hash secretKey group tree child message) =
      leafRoot hash secretKey group tree child.val := by
  simp only [recoverLeaf, signUpper, leafRoot]
  congr 1
  funext chain
  have hd : (digit message chain).val ≤ 3 := by have := (digit message chain).isLt; omega
  simpa [endpoint, Nat.add_sub_of_le hd] using
    (walk_append (chainHash hash group tree child.val chain) 0 (digit message chain).val
      (3 - (digit message chain).val) (secret hash secretKey group tree child.val chain)).symm

theorem recover_upper_sign (hash : Hash) (secretKey : SecretKey) (group tree : Nat)
    (child : Fin 8) (message : Digest) :
    recoverUpper hash group tree child message (signUpper hash secretKey group tree child message) =
      root hash secretKey group tree := by
  unfold recoverUpper
  simp only [recover_leaf_sign]
  fin_cases child <;>
    simp [signUpper, root, quad, pair, Nat.reduceDiv, Nat.reduceMod]

def bottomSecret (hash : Hash) (secretKey : SecretKey) (child : Nat) : Digest :=
  truncate (query hash 1 0 child 0 0 0 (bytes secretKey))

def bottomLeaf (hash : Hash) (secretKey : SecretKey) (child : Nat) : Digest :=
  truncate (query hash 2 0 child 0 0 0 (bytes (bottomSecret hash secretKey child)))

def bottomPair (hash : Hash) (secretKey : SecretKey) (index : Nat) : Digest :=
  node hash 0 index (bottomLeaf hash secretKey (2 * index))
    (bottomLeaf hash secretKey (2 * index + 1))

def bottomQuad (hash : Hash) (secretKey : SecretKey) (index : Nat) : Digest :=
  node hash 1 index (bottomPair hash secretKey (2 * index))
    (bottomPair hash secretKey (2 * index + 1))

def bottomOct (hash : Hash) (secretKey : SecretKey) (index : Nat) : Digest :=
  node hash 2 index (bottomQuad hash secretKey (2 * index))
    (bottomQuad hash secretKey (2 * index + 1))

def bottomRoot (hash : Hash) (secretKey : SecretKey) : Digest :=
  node hash 3 0 (bottomOct hash secretKey 0) (bottomOct hash secretKey 1)

structure BottomSignature where
  seed : Digest
  sibling0 : Digest
  sibling1 : Digest
  sibling2 : Digest
  sibling3 : Digest

def signBottom (hash : Hash) (secretKey : SecretKey) (child : Fin 16) : BottomSignature where
  seed := bottomSecret hash secretKey child.val
  sibling0 := bottomLeaf hash secretKey (if child.val % 2 = 0 then child.val + 1 else child.val - 1)
  sibling1 := bottomPair hash secretKey
    (if child.val / 2 % 2 = 0 then child.val / 2 + 1 else child.val / 2 - 1)
  sibling2 := bottomQuad hash secretKey
    (if child.val / 4 % 2 = 0 then child.val / 4 + 1 else child.val / 4 - 1)
  sibling3 := bottomOct hash secretKey (if child.val / 8 = 0 then 1 else 0)

def recoverBottom (hash : Hash) (child : Fin 16) (signature : BottomSignature) : Digest :=
  let leaf := truncate (query hash 2 0 child.val 0 0 0 (bytes signature.seed))
  let first := if child.val % 2 = 0 then node hash 0 (child.val / 2) leaf signature.sibling0
    else node hash 0 (child.val / 2) signature.sibling0 leaf
  let second := if child.val / 2 % 2 = 0 then
    node hash 1 (child.val / 4) first signature.sibling1
    else node hash 1 (child.val / 4) signature.sibling1 first
  let third := if child.val / 4 % 2 = 0 then
    node hash 2 (child.val / 8) second signature.sibling2
    else node hash 2 (child.val / 8) signature.sibling2 second
  if child.val / 8 = 0 then node hash 3 0 third signature.sibling3
    else node hash 3 0 signature.sibling3 third

theorem recover_bottom_sign (hash : Hash) (secretKey : SecretKey) (child : Fin 16) :
    recoverBottom hash child (signBottom hash secretKey child) = bottomRoot hash secretKey := by
  fin_cases child <;>
    simp [recoverBottom, signBottom, bottomRoot, bottomOct, bottomQuad, bottomPair,
      bottomLeaf, Nat.reduceDiv, Nat.reduceMod]

def signLayers (hash : Hash) (secretKey : SecretKey) :
    Nat → Nat → Nat → Digest → List UpperSignature
  | 0, _, _, _ => []
  | count + 1, group, index, message =>
      let tree := index / 8
      signUpper hash secretKey group tree ⟨index % 8, Nat.mod_lt _ (by decide)⟩ message ::
        signLayers hash secretKey count (group + 1) tree (root hash secretKey group tree)

def recoverLayers (hash : Hash) :
    Nat → Nat → Digest → List UpperSignature → Digest
  | _, _, message, [] => message
  | group, index, message, signature :: rest =>
      recoverLayers hash (group + 1) (index / 8)
        (recoverUpper hash group (index / 8) ⟨index % 8, Nat.mod_lt _ (by decide)⟩
          message signature) rest

def rootsAfter (hash : Hash) (secretKey : SecretKey) :
    Nat → Nat → Nat → Digest → Digest
  | 0, _, _, message => message
  | count + 1, group, index, _ =>
      rootsAfter hash secretKey count (group + 1) (index / 8)
        (root hash secretKey group (index / 8))

theorem recover_sign_layers (hash : Hash) (secretKey : SecretKey)
    (count group index : Nat) (message : Digest) :
    recoverLayers hash group index message
      (signLayers hash secretKey count group index message) =
      rootsAfter hash secretKey count group index message := by
  induction count generalizing group index message with
  | zero => rfl
  | succ count ih =>
    simp only [signLayers, recoverLayers, rootsAfter]
    rw [recover_upper_sign]
    exact ih _ _ _

theorem roots_after_succ (hash : Hash) (secretKey : SecretKey)
    (count group index : Nat) (message : Digest) :
    rootsAfter hash secretKey (count + 1) group index message =
      root hash secretKey (group + count) (index / 8 ^ (count + 1)) := by
  induction count generalizing group index message with
  | zero => simp [rootsAfter]
  | succ count ih =>
    rw [rootsAfter, ih]
    simp [Nat.div_div_eq_div_mul, pow_succ, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_comm]

theorem sign_layers_length (hash : Hash) (secretKey : SecretKey)
    (count group index : Nat) (message : Digest) :
    (signLayers hash secretKey count group index message).length = count := by
  induction count generalizing group index message with
  | zero => rfl
  | succ count ih => simp [signLayers, ih]

structure Signature where
  randomizer : Bytes 32
  bottom : BottomSignature
  upper : List UpperSignature

def keygen (hash : Hash) (secretKey : SecretKey) : PublicKey :=
  root hash secretKey 51 0

def sign (hash : Hash) (secretKey : SecretKey) (message : Message) : Signature :=
  let randomizer := Reference.randomizer hash secretKey message
  let index := (Reference.indexOf hash message randomizer).toNat
  ⟨randomizer,
    signBottom hash secretKey ⟨index % 16, Nat.mod_lt _ (by decide)⟩,
    signLayers hash secretKey 52 0 (index / 16) (bottomRoot hash secretKey)⟩

def verify (hash : Hash) (pk : PublicKey) (message : Message)
    (signature : Signature) : Prop :=
  signature.upper.length = 52 ∧
    let index := (Reference.indexOf hash message signature.randomizer).toNat
    recoverLayers hash 0 (index / 16)
      (recoverBottom hash ⟨index % 16, Nat.mod_lt _ (by decide)⟩ signature.bottom)
      signature.upper = pk

theorem correct (hash : Hash) (secretKey : SecretKey) (message : Message) :
    verify hash (keygen hash secretKey) message (sign hash secretKey message) := by
  constructor
  · exact sign_layers_length _ _ _ _ _ _
  · simp only [sign, keygen, recover_bottom_sign, recover_sign_layers]
    rw [roots_after_succ hash secretKey 51 0]
    have hcap : (16 : Nat) * 8 ^ 52 = 2 ^ 160 := by decide
    have hindex : (Reference.indexOf hash message (Reference.randomizer hash secretKey message)).toNat / 16 <
        8 ^ 52 := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).2
      rw [Nat.mul_comm, hcap]
      exact (Reference.indexOf hash message (Reference.randomizer hash secretKey message)).isLt
    simp only [Nat.zero_add, Nat.div_eq_of_lt hindex]

def upperBytes (signature : UpperSignature) : List Byte :=
  (List.ofFn signature.values).flatMap bytes ++
    bytes signature.sibling0 ++ bytes signature.sibling1 ++ bytes signature.sibling2

def bottomBytes (signature : BottomSignature) : List Byte :=
  bytes signature.seed ++ bytes signature.sibling0 ++ bytes signature.sibling1 ++
    bytes signature.sibling2 ++ bytes signature.sibling3

def Signature.encode (signature : Signature) : List Byte :=
  bytes signature.randomizer ++ bottomBytes signature.bottom ++ signature.upper.flatMap upperBytes

def Signature.Valid (signature : Signature) : Prop := signature.upper.length = 52

theorem upper_bytes_length (signature : UpperSignature) : (upperBytes signature).length = 1136 := by
  simp [upperBytes, bytes]

theorem bottom_bytes_length (signature : BottomSignature) : (bottomBytes signature).length = 80 := by
  simp [bottomBytes, bytes]

theorem upper_bytes_injective : Function.Injective upperBytes := by
  intro first second heq
  have prefixLength :
      ((List.ofFn first.values).flatMap bytes).length =
      ((List.ofFn second.values).flatMap bytes).length := by simp [bytes]
  simp only [upperBytes, List.append_assoc] at heq
  have valuesBytes := List.append_inj_left heq prefixLength
  have rest := List.append_inj_right heq prefixLength
  have values := SignatureEncoding.flatMap_injective (bytes (n := 16)) 16
    (by decide) (fun _ => by simp) (SecurityPacking.bytes_injective 16) valuesBytes
  have valuesEq := List.ofFn_injective values
  have sibling0Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_left rest (by simp [bytes]))
  have rest1 := List.append_inj_right rest (by simp [bytes])
  have sibling1Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_left rest1 (by simp [bytes]))
  have sibling2Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_right rest1 (by simp [bytes]))
  cases first
  cases second
  cases valuesEq
  cases sibling0Eq
  cases sibling1Eq
  cases sibling2Eq
  rfl

theorem bottom_bytes_injective : Function.Injective bottomBytes := by
  intro first second heq
  simp only [bottomBytes, List.append_assoc] at heq
  have seedEq := SecurityPacking.bytes_injective 16
    (List.append_inj_left heq (by simp [bytes]))
  have rest0 := List.append_inj_right heq (by simp [bytes])
  have sibling0Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_left rest0 (by simp [bytes]))
  have rest1 := List.append_inj_right rest0 (by simp [bytes])
  have sibling1Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_left rest1 (by simp [bytes]))
  have rest2 := List.append_inj_right rest1 (by simp [bytes])
  have sibling2Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_left rest2 (by simp [bytes]))
  have sibling3Eq := SecurityPacking.bytes_injective 16
    (List.append_inj_right rest2 (by simp [bytes]))
  cases first
  cases second
  cases seedEq
  cases sibling0Eq
  cases sibling1Eq
  cases sibling2Eq
  cases sibling3Eq
  rfl

theorem signature_encode_injective : Function.Injective Signature.encode := by
  intro first second heq
  simp only [Signature.encode, List.append_assoc] at heq
  have randomizerEq := SecurityPacking.bytes_injective 32
    (List.append_inj_left heq (by simp [bytes]))
  have rest := List.append_inj_right heq (by simp [bytes])
  have bottomEq := bottom_bytes_injective
    (List.append_inj_left rest (by simp [bottom_bytes_length]))
  have upperEq := SignatureEncoding.flatMap_injective upperBytes 1136
    (by decide) upper_bytes_length upper_bytes_injective
    (List.append_inj_right rest (by simp [bottom_bytes_length]))
  cases first
  cases second
  cases randomizerEq
  cases bottomEq
  cases upperEq
  rfl

theorem signature_bytes_length (signature : Signature) (valid : signature.Valid) :
    signature.encode.length = 59184 := by
  simp only [Signature.encode, List.length_append, bottom_bytes_length,
    List.length_flatMap]
  rw [show (bytes signature.randomizer).length = 32 by simp [bytes]]
  have upper : (signature.upper.map (fun item => (upperBytes item).length)).sum =
      1136 * signature.upper.length := by
    simp [upper_bytes_length, List.sum_replicate, Nat.mul_comm]
  rw [upper]
  rw [show signature.upper.length = 52 from valid]

/-- Cost target for a fused bytecode signer that computes each leaf once,
including seven internal nodes per upper tree, fifteen bottom nodes, the
randomizer and index compressions. This is not a bytecode execution proof. -/
def signCompressions : Nat := 52 * (8 * (68 * 4 + 18) + 7) + (16 * 2 + 15) + 9

theorem sign_budget : signCompressions = 121060 ∧ signCompressions < BUDGET_SIGN := by
  decide

/-- A safe checksum-independent verification cost target. The actual checksum
bound is tighter because its digits cannot all incur three suffix hashes. -/
def verifyCompressions : Nat := 52 * (68 * 3 + 18 + 3) + 5 + 4

theorem verify_compressions_bound : verifyCompressions = 11709 := by decide

end SigGolfCandidate.Hypertree.GroupedHeightThree
