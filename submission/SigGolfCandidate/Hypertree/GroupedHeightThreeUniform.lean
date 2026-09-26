import SigGolfCandidate.Hypertree.GroupedUniformTableBound
import SigGolfCandidate.Hypertree.GroupedHeightThree

/-! Inlined from SigGolfCandidate.Hypertree.GroupedUniformGreedy; its only importer was SigGolfCandidate.Hypertree.GroupedHeightThreeUniform. -/
section
namespace SigGolfCandidate.Hypertree.GroupedUniformGreedy
open Finset SigGolfCandidate.Hypertree.GroupedUniformCapacity
open SigGolfCandidate.Hypertree.GroupedUniformTableBound

/-- Number of valid suffix words preceding the branch labeled `d`. -/
def branchPrefix (n s d : Nat) : Nat :=
  ∑ i ∈ Finset.range d, if i ≤ s then count n (s - i) else 0

theorem prefix_succ (n s d : Nat) :
    branchPrefix n s (d+1) = branchPrefix n s d + if d ≤ s then count n (s-d) else 0 := by
  simp only [branchPrefix, Finset.sum_range_succ]

theorem prefix_six (n s : Nat) : branchPrefix n s 6 = count (n+1) s := by
  exact (count_succ_six n s).symm

/-- The first cumulative interval containing a legal rank supplies a valid
next digit and a residual rank within the chosen suffix block. -/
def round (n s r : Nat) (rank : r < count (n+1) s) :
    { d : Nat // d < 6 ∧ d ≤ s ∧ branchPrefix n s d ≤ r ∧
      r - branchPrefix n s d < count n (s-d) } := by
  let P : Nat → Prop := fun d => r < branchPrefix n s (d+1)
  have h5 : P 5 := by
    change r < branchPrefix n s (5 + 1)
    rw [show 5 + 1 = 6 by decide, prefix_six]
    exact rank
  have hex : ∃ d, P d := ⟨5, h5⟩
  let d := Nat.find hex
  have hspec : P d := Nat.find_spec hex
  have hd : d < 6 := by
    have hbound : d ≤ 5 := Nat.find_min' hex h5
    omega
  have hprefix : branchPrefix n s d ≤ r := by
    by_cases hzero : d = 0
    · rw [hzero]
      simp [branchPrefix]
    · have hmin := Nat.find_min hex (show d - 1 < d by omega)
      have hprev : d - 1 + 1 = d := by omega
      change ¬ r < branchPrefix n s (d - 1 + 1) at hmin
      rw [hprev] at hmin
      omega
  have hbranch : r < branchPrefix n s d + if d ≤ s then count n (s-d) else 0 := by
    simpa only [P, prefix_succ] using hspec
  have hds : d ≤ s := by
    by_contra h
    simp only [if_neg h, add_zero] at hbranch
    omega
  refine ⟨d, hd, hds, hprefix, ?_⟩
  simp only [if_pos hds] at hbranch
  omega

theorem greedy_round (n s r : Nat) (rank : r < count (n+1) s) :
    ∃ d : Nat, d < 6 ∧ d ≤ s ∧ branchPrefix n s d ≤ r ∧
      r - branchPrefix n s d < count n (s-d) :=
  ⟨(round n s r rank).val, (round n s r rank).property⟩



/-- Greedy unranking follows one certified cumulative-count interval per digit. -/
def unrank : (n s r : Nat) → r < count n s → List Nat
  | 0, _, _, _ => []
  | n + 1, s, r, hr =>
      let chosen := round n s r hr
      chosen.val :: unrank n (s - chosen.val)
        (r - branchPrefix n s chosen.val) chosen.property.2.2.2

/-- Rank in the same branch order used by `round`. -/
def rankCode : Nat → Nat → List Nat → Nat
  | 0, _, _ => 0
  | _n + 1, _s, [] => 0
  | n + 1, s, d :: tail => branchPrefix n s d + rankCode n (s - d) tail

theorem rank_unrank (n s r : Nat) (hr : r < count n s) :
    rankCode n s (unrank n s r hr) = r := by
  induction n generalizing s r with
  | zero =>
      have hzero : r = 0 := by
        simp only [count] at hr
        split_ifs at hr <;> omega
      subst r
      rfl
  | succ n ih =>
      let chosen := round n s r hr
      have hchild := chosen.property.2.2.2
      change branchPrefix n s chosen.val +
        rankCode n (s - chosen.val)
          (unrank n (s - chosen.val) (r - branchPrefix n s chosen.val) hchild) = r
      rw [ih]
      have hprefix := chosen.property.2.2.1
      omega

theorem unrank_valid (n s r : Nat) (hr : r < count n s) :
    Valid n s (unrank n s r hr) := by
  induction n generalizing s r with
  | zero =>
      have hs : s = 0 := by
        simp only [count] at hr
        split_ifs at hr with h
        · exact h
        · omega
      subst s
      simp [Valid, unrank]
  | succ n ih =>
      let chosen := round n s r hr
      have hchild := chosen.property.2.2.2
      obtain ⟨hlen, hsum, hbound⟩ := ih (s - chosen.val)
        (r - branchPrefix n s chosen.val) hchild
      change Valid (n + 1) s
        (chosen.val :: unrank n (s - chosen.val)
          (r - branchPrefix n s chosen.val) hchild)
      dsimp only [Valid]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [List.length_cons] using congrArg Nat.succ hlen
      · simp only [List.sum_cons, hsum]
        have hle := chosen.property.2.1
        omega
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | htail
        · exact chosen.property.1
        · exact hbound d htail

def encodeGreedy (digest : BitVec 128) : List Nat :=
  unrank 52 147 digest.toNat (lt_of_lt_of_le digest.isLt capacity)

theorem encodeGreedy_valid (digest : BitVec 128) :
    Valid 52 147 (encodeGreedy digest) :=
  unrank_valid 52 147 digest.toNat (lt_of_lt_of_le digest.isLt capacity)

theorem encodeGreedy_injective : Function.Injective encodeGreedy := by
  intro x y same
  have h := congrArg (rankCode 52 147) same
  simp only [encodeGreedy, rank_unrank] at h
  exact BitVec.eq_of_toNat_eq h


/-- WOTS chain digit selected by the constructive greedy encoder. -/
def encodedDigit (digest : BitVec 128) (i : Fin 52) : Nat :=
  (encodeGreedy digest)[i.val]'(by
    rw [(encodeGreedy_valid digest).1]
    exact i.isLt)

theorem distinct_digest_has_earlier_digit (x y : BitVec 128) (different : x ≠ y) :
    ∃ i : Fin 52, encodedDigit y i < encodedDigit x i := by
  by_contra noEarlier
  push Not at noEarlier
  have ordered : List.Forall₂ (fun a b : Nat => a ≤ b)
      (encodeGreedy x) (encodeGreedy y) := by
    apply (List.forall₂_iff_get).2
    constructor
    · rw [(encodeGreedy_valid x).1, (encodeGreedy_valid y).1]
    · intro i hiX hiY
      have hi : i < 52 := by simpa only [(encodeGreedy_valid x).1] using hiX
      have h := noEarlier ⟨i, hi⟩
      change encodedDigit x ⟨i, hi⟩ ≤ encodedDigit y ⟨i, hi⟩ at h
      unfold encodedDigit at h
      omega
  have sameWords : encodeGreedy x = encodeGreedy y :=
    fixed_weight_antichain ordered
      (by rw [(encodeGreedy_valid x).2.1, (encodeGreedy_valid y).2.1])
  exact different (encodeGreedy_injective sameWords)

end SigGolfCandidate.Hypertree.GroupedUniformGreedy

end

/-!
An isolated functional prototype for the 160-bit grouped hypertree. The bottom
uses a tree-addressed height-four preimage tree. Each of the 52 upper groups uses
a height-three tree and a 52-chain, radix-six WOTS leaf. The message code is the certified
fixed-weight code of `GroupedUniformGreedy`.

Two adjacent 16-byte chain secrets are the low and high halves of one 32-byte
random-oracle answer. This is a cost optimization of the signer, not a security
theorem for the paired-source oracle; that theorem and bytecode refinement remain
separate obligations before this prototype can replace the active candidate.
-/

namespace SigGolfCandidate.Hypertree.GroupedHeightThreeUniform
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192

abbrev Chain6 := Fin 52

def digit (message : Digest) (chain : Chain6) : Fin 6 :=
  ⟨GroupedUniformGreedy.encodedDigit message chain % 6, Nat.mod_lt _ (by decide)⟩

theorem encoded_digit_lt_six (message : Digest) (chain : Chain6) :
    GroupedUniformGreedy.encodedDigit message chain < 6 := by
  unfold GroupedUniformGreedy.encodedDigit
  exact (GroupedUniformGreedy.encodeGreedy_valid message).2.2 _ (List.getElem_mem _)

theorem digit_eq_encoded (message : Digest) (chain : Chain6) :
    (digit message chain).val = GroupedUniformGreedy.encodedDigit message chain := by
  simp [digit, Nat.mod_eq_of_lt (encoded_digit_lt_six message chain)]

theorem digit_weight (message : Digest) :
    ∑ chain : Chain6, (digit message chain).val = 147 := by
  have valid := GroupedUniformGreedy.encodeGreedy_valid message
  have hlist :
      (List.ofFn fun chain : Chain6 => GroupedUniformGreedy.encodedDigit message chain) =
        GroupedUniformGreedy.encodeGreedy message := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using valid.1.symm
    · intro i hi hj
      simp only [List.getElem_ofFn, GroupedUniformGreedy.encodedDigit]
  calc
    _ = ∑ chain : Chain6, GroupedUniformGreedy.encodedDigit message chain := by
      apply Finset.sum_congr rfl
      intro chain _
      exact digit_eq_encoded message chain
    _ = (List.ofFn fun chain : Chain6 =>
        GroupedUniformGreedy.encodedDigit message chain).sum := by
      rw [List.sum_ofFn]
    _ = 147 := by rw [hlist]; exact valid.2.1

theorem suffix_weight (message : Digest) :
    (∑ chain : Chain6, (5 - (digit message chain).val)) = 113 := by
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, digit_weight]
    omega
  · intro chain _
    have := (digit message chain).isLt
    omega

def base (group : Nat) : Nat := 4 + 3 * group
def leafAddress (tree child : Nat) : Nat := 8 * tree + child

def secretPair (hash : Hash) (secretKey : SecretKey) (group tree child pair : Nat) :
    BitVec 256 :=
  query hash 1 (base group) (leafAddress tree child) 0 pair 0 (bytes secretKey)

def secret (hash : Hash) (secretKey : SecretKey) (group tree child : Nat)
    (chain : Chain6) : Digest :=
  let answer := secretPair hash secretKey group tree child (chain.val / 2)
  if chain.val % 2 = 0 then answer.extractLsb' 0 128
    else answer.extractLsb' 128 128

def chainHash (hash : Hash) (group tree child : Nat) (chain : Chain6)
    (step : Nat) (value : Digest) : Digest :=
  truncate (query hash 2 (base group) (leafAddress tree child) 0 chain.val step
    (bytes value))

def endpoint (hash : Hash) (secretKey : SecretKey) (group tree child : Nat)
    (chain : Chain6) : Digest :=
  walk (chainHash hash group tree child chain) 0 5
    (secret hash secretKey group tree child chain)

def compressLeaf (hash : Hash) (group tree child : Nat)
    (values : Chain6 → Digest) : Digest :=
  truncate (query hash 3 (base group) (leafAddress tree child) 0 0 0
    ((List.ofFn values).flatMap bytes))

def leafRoot (hash : Hash) (secretKey : SecretKey) (group tree child : Nat) : Digest :=
  compressLeaf hash group tree child (endpoint hash secretKey group tree child)

def node (hash : Hash) (level tree : Nat) (left right : Digest) : Digest :=
  GroupedHeightThree.node hash level tree left right

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
  values : Chain6 → Digest
  sibling0 : Digest
  sibling1 : Digest
  sibling2 : Digest

def signUpper (hash : Hash) (secretKey : SecretKey) (group tree : Nat)
    (child : Fin 8) (message : Digest) : UpperSignature where
  values := fun chain => walk (chainHash hash group tree child.val chain) 0
    (digit message chain).val (secret hash secretKey group tree child.val chain)
  sibling0 := leafRoot hash secretKey group tree
    (if child.val % 2 = 0 then child.val + 1 else child.val - 1)
  sibling1 := pair hash secretKey group tree
    (if child.val / 2 % 2 = 0 then child.val / 2 + 1 else child.val / 2 - 1)
  sibling2 := quad hash secretKey group tree (if child.val / 4 = 0 then 1 else 0)

def recoverLeaf (hash : Hash) (group tree child : Nat) (message : Digest)
    (signature : UpperSignature) : Digest :=
  compressLeaf hash group tree child (fun chain =>
    walk (chainHash hash group tree child chain) (digit message chain).val
      (5 - (digit message chain).val) (signature.values chain))

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
    recoverLeaf hash group tree child.val message
      (signUpper hash secretKey group tree child message) =
      leafRoot hash secretKey group tree child.val := by
  simp only [recoverLeaf, signUpper, leafRoot]
  congr 1
  funext chain
  have hd : (digit message chain).val ≤ 5 := by
    have := (digit message chain).isLt
    omega
  simpa [endpoint, Nat.add_sub_of_le hd] using
    (walk_append (chainHash hash group tree child.val chain) 0
      (digit message chain).val (5 - (digit message chain).val)
      (secret hash secretKey group tree child.val chain)).symm

theorem recover_upper_sign (hash : Hash) (secretKey : SecretKey) (group tree : Nat)
    (child : Fin 8) (message : Digest) :
    recoverUpper hash group tree child message
      (signUpper hash secretKey group tree child message) =
      root hash secretKey group tree := by
  unfold recoverUpper
  simp only [recover_leaf_sign]
  fin_cases child <;>
    simp [signUpper, root, quad, pair, Nat.reduceDiv, Nat.reduceMod]

def bottomSecret (hash : Hash) (secretKey : SecretKey) (tree child : Nat) : Digest :=
  truncate (query hash 1 0 (16 * tree + child) 0 0 0 (bytes secretKey))

def bottomLeaf (hash : Hash) (secretKey : SecretKey) (tree child : Nat) : Digest :=
  truncate (query hash 2 0 (16 * tree + child) 0 0 0
    (bytes (bottomSecret hash secretKey tree child)))

def bottomPair (hash : Hash) (secretKey : SecretKey) (tree index : Nat) : Digest :=
  node hash 0 (8 * tree + index) (bottomLeaf hash secretKey tree (2 * index))
    (bottomLeaf hash secretKey tree (2 * index + 1))

def bottomQuad (hash : Hash) (secretKey : SecretKey) (tree index : Nat) : Digest :=
  node hash 1 (4 * tree + index) (bottomPair hash secretKey tree (2 * index))
    (bottomPair hash secretKey tree (2 * index + 1))

def bottomOct (hash : Hash) (secretKey : SecretKey) (tree index : Nat) : Digest :=
  node hash 2 (2 * tree + index) (bottomQuad hash secretKey tree (2 * index))
    (bottomQuad hash secretKey tree (2 * index + 1))

def bottomRoot (hash : Hash) (secretKey : SecretKey) (tree : Nat) : Digest :=
  node hash 3 tree (bottomOct hash secretKey tree 0)
    (bottomOct hash secretKey tree 1)

structure BottomSignature where
  seed : Digest
  sibling0 : Digest
  sibling1 : Digest
  sibling2 : Digest
  sibling3 : Digest

def signBottom (hash : Hash) (secretKey : SecretKey) (tree : Nat)
    (child : Fin 16) : BottomSignature where
  seed := bottomSecret hash secretKey tree child.val
  sibling0 := bottomLeaf hash secretKey tree
    (if child.val % 2 = 0 then child.val + 1 else child.val - 1)
  sibling1 := bottomPair hash secretKey tree
    (if child.val / 2 % 2 = 0 then child.val / 2 + 1 else child.val / 2 - 1)
  sibling2 := bottomQuad hash secretKey tree
    (if child.val / 4 % 2 = 0 then child.val / 4 + 1 else child.val / 4 - 1)
  sibling3 := bottomOct hash secretKey tree (if child.val / 8 = 0 then 1 else 0)

def recoverBottom (hash : Hash) (tree : Nat) (child : Fin 16)
    (signature : BottomSignature) : Digest :=
  let leaf := truncate (query hash 2 0 (16 * tree + child.val) 0 0 0
    (bytes signature.seed))
  let first := if child.val % 2 = 0 then
    node hash 0 (8 * tree + child.val / 2) leaf signature.sibling0
    else node hash 0 (8 * tree + child.val / 2) signature.sibling0 leaf
  let second := if child.val / 2 % 2 = 0 then
    node hash 1 (4 * tree + child.val / 4) first signature.sibling1
    else node hash 1 (4 * tree + child.val / 4) signature.sibling1 first
  let third := if child.val / 4 % 2 = 0 then
    node hash 2 (2 * tree + child.val / 8) second signature.sibling2
    else node hash 2 (2 * tree + child.val / 8) signature.sibling2 second
  if child.val / 8 = 0 then node hash 3 tree third signature.sibling3
    else node hash 3 tree signature.sibling3 third

theorem recover_bottom_sign (hash : Hash) (secretKey : SecretKey)
    (tree : Nat) (child : Fin 16) :
    recoverBottom hash tree child (signBottom hash secretKey tree child) =
      bottomRoot hash secretKey tree := by
  fin_cases child <;>
    simp [recoverBottom, signBottom, bottomRoot, bottomOct, bottomQuad,
      bottomPair, bottomLeaf, Nat.reduceDiv, Nat.reduceMod]

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
        (recoverUpper hash group (index / 8)
          ⟨index % 8, Nat.mod_lt _ (by decide)⟩ message signature) rest

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
    signBottom hash secretKey (index / 16)
      ⟨index % 16, Nat.mod_lt _ (by decide)⟩,
    signLayers hash secretKey 52 0 (index / 16)
      (bottomRoot hash secretKey (index / 16))⟩

def verify (hash : Hash) (pk : PublicKey) (message : Message)
    (signature : Signature) : Prop :=
  signature.upper.length = 52 ∧
    let index := (Reference.indexOf hash message signature.randomizer).toNat
    recoverLayers hash 0 (index / 16)
      (recoverBottom hash (index / 16)
        ⟨index % 16, Nat.mod_lt _ (by decide)⟩ signature.bottom)
      signature.upper = pk

theorem correct (hash : Hash) (secretKey : SecretKey) (message : Message) :
    verify hash (keygen hash secretKey) message (sign hash secretKey message) := by
  constructor
  · exact sign_layers_length _ _ _ _ _ _
  · simp only [sign, keygen, recover_bottom_sign,
      recover_sign_layers]
    rw [roots_after_succ hash secretKey 51 0]
    have hcap : (16 : Nat) * 8 ^ 52 = 2 ^ 160 := by decide
    have hindex :
        (Reference.indexOf hash message
          (Reference.randomizer hash secretKey message)).toNat / 16 < 8 ^ 52 := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).2
      rw [Nat.mul_comm, hcap]
      exact (Reference.indexOf hash message
        (Reference.randomizer hash secretKey message)).isLt
    simp only [Nat.zero_add, Nat.div_eq_of_lt hindex]

def upperBytes (signature : UpperSignature) : List Byte :=
  (List.ofFn signature.values).flatMap bytes ++
    bytes signature.sibling0 ++ bytes signature.sibling1 ++ bytes signature.sibling2

def bottomBytes (signature : BottomSignature) : List Byte :=
  bytes signature.seed ++ bytes signature.sibling0 ++ bytes signature.sibling1 ++
    bytes signature.sibling2 ++ bytes signature.sibling3

theorem bottom_bytes_length (signature : BottomSignature) :
    (bottomBytes signature).length = 80 := by
  simp [bottomBytes, bytes]

def Signature.encode (signature : Signature) : List Byte :=
  bytes signature.randomizer ++ bottomBytes signature.bottom ++
    signature.upper.flatMap upperBytes

def Signature.Valid (signature : Signature) : Prop := signature.upper.length = 52

theorem upper_bytes_length (signature : UpperSignature) :
    (upperBytes signature).length = 880 := by
  simp [upperBytes, bytes]

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
  have upperEq := SignatureEncoding.flatMap_injective upperBytes 880
    (by decide) upper_bytes_length upper_bytes_injective
    (List.append_inj_right rest (by simp [bottom_bytes_length]))
  cases first
  cases second
  cases randomizerEq
  cases bottomEq
  cases upperEq
  rfl

theorem signature_bytes_length (signature : Signature) (valid : signature.Valid) :
    signature.encode.length = 45872 := by
  simp only [Signature.encode, List.length_append,
    bottom_bytes_length, List.length_flatMap]
  rw [show (bytes signature.randomizer).length = 32 by simp [bytes]]
  have upper : (signature.upper.map (fun item => (upperBytes item).length)).sum =
      880 * signature.upper.length := by
    simp [upper_bytes_length, List.sum_replicate, Nat.mul_comm]
  rw [upper]
  rw [show signature.upper.length = 52 from valid]

/-- This is a target count for a fused signer, not a bytecode cost proof. -/
def signCompressions : Nat := 52 * (8 * (26 + 52 * 5 + 14) + 7) + 47 + 9

theorem sign_budget : signCompressions = 125220 ∧
    signCompressions < BUDGET_SIGN := by decide

/-- Constant-weight codewords require exactly 113 WOTS suffix hashes. -/
def verifyCompressions : Nat := 52 * (113 + 14 + 3) + 5 + 4

theorem verify_compressions : verifyCompressions = 6769 := by decide

end SigGolfCandidate.Hypertree.GroupedHeightThreeUniform
