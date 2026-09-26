import SigGolfCandidate.Hypertree.GroupedUpperTree
import SigGolfCandidate.Hypertree.GroupedBottomTree
import SigGolfCandidate.Hypertree.GroupedMixedIndex

/-!
Functional composition of one tree-addressed height-ten bottom tree and 49
upper radix-six WOTS groups. Heights are 46 threes followed by three fours.
The structured signatures have 43,376 encoded bytes. This module establishes
honest recovery for every oracle; security and the four exact RISC-V images
remain separate certificate obligations.
-/

namespace SigGolfCandidate.Hypertree.GroupedMixedScheme
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192

abbrev Heights := GroupedMixedIndex.upperHeights

inductive UpperWitnesses : List Nat → Type where
  | nil : UpperWitnesses []
  | cons {height : Nat} {rest : List Nat}
      (head : GroupedUpperTree.Witness height) (tail : UpperWitnesses rest) :
      UpperWitnesses (height :: rest)

def UpperWitnesses.encode : {heights : List Nat} → UpperWitnesses heights → List Byte
  | [], .nil => []
  | _ :: _, .cons head tail => head.encode ++ tail.encode

theorem UpperWitnesses.encode_length : {heights : List Nat} →
    (witnesses : UpperWitnesses heights) →
    witnesses.encode.length = 16 * (52 * heights.length + heights.sum)
  | [], .nil => by simp [UpperWitnesses.encode]
  | height :: rest, .cons head tail => by
      simp only [UpperWitnesses.encode, List.length_append]
      rw [GroupedUpperTree.Witness.encode_length head,
        UpperWitnesses.encode_length tail]
      simp only [List.length_cons, List.sum_cons]
      omega

theorem UpperWitnesses.encode_injective {heights : List Nat} :
    Function.Injective (UpperWitnesses.encode : UpperWitnesses heights → List Byte) := by
  intro first second same
  induction first with
  | nil => cases second; rfl
  | cons head tail ih =>
      cases second with
      | cons other otherTail =>
          simp only [UpperWitnesses.encode] at same
          have lengths : head.encode.length = other.encode.length := by
            rw [GroupedUpperTree.Witness.encode_length head,
              GroupedUpperTree.Witness.encode_length other]
          have headBytes := List.append_inj_left same lengths
          have tailBytes := List.append_inj_right same lengths
          have headEq := GroupedUpperTree.Witness.encode_injective headBytes
          have tailEq := ih tailBytes
          cases headEq
          cases tailEq
          rfl

def signLayers (hash : Hash) (secretKey : SecretKey) :
    (heights : List Nat) → (base index : Nat) → Digest → UpperWitnesses heights
  | [], _, _, _ => .nil
  | height :: rest, base, index, message =>
      let tree := index / 2 ^ height
      let built := GroupedUpperTree.build hash secretKey base height tree index message
      .cons built.witness
        (signLayers hash secretKey rest (base + height) tree built.root)

def recoverLayers (hash : Hash) :
    (heights : List Nat) → (base index : Nat) → Digest →
      UpperWitnesses heights → Digest
  | [], _, _, message, .nil => message
  | height :: rest, base, index, message, .cons head tail =>
      let tree := index / 2 ^ height
      recoverLayers hash rest (base + height) tree
        (GroupedUpperTree.recover hash base height tree index message head) tail

def rootsAfter (hash : Hash) (secretKey : SecretKey) :
    (heights : List Nat) → (base index : Nat) → Digest → Digest
  | [], _, _, message => message
  | height :: rest, base, index, _ =>
      let tree := index / 2 ^ height
      rootsAfter hash secretKey rest (base + height) tree
        (GroupedUpperTree.root hash secretKey base height tree)

theorem recover_sign_layers (hash : Hash) (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat) (message : Digest) :
    recoverLayers hash heights base index message
      (signLayers hash secretKey heights base index message) =
      rootsAfter hash secretKey heights base index message := by
  induction heights generalizing base index message with
  | nil => rfl
  | cons height rest ih =>
      simp only [signLayers, recoverLayers, rootsAfter]
      rw [GroupedUpperTree.recover_build, GroupedUpperTree.build_root]
      exact ih _ _ _

theorem roots_after_append (hash : Hash) (secretKey : SecretKey)
    (initial remaining : List Nat) (base index : Nat) (message : Digest) :
    rootsAfter hash secretKey (initial ++ remaining) base index message =
      rootsAfter hash secretKey remaining (base + initial.sum)
        (index / 2 ^ initial.sum)
        (rootsAfter hash secretKey initial base index message) := by
  induction initial generalizing base index message with
  | nil => simp [rootsAfter]
  | cons height rest ih =>
      simp only [List.cons_append, List.sum_cons, rootsAfter]
      rw [ih]
      simp only [Nat.div_div_eq_div_mul, pow_add]
      congr 1; omega

def prefixHeights : List Nat := List.replicate 46 3 ++ List.replicate 2 4

theorem heights_split : Heights = prefixHeights ++ [4] := by decide
theorem prefix_height_sum : prefixHeights.sum = 146 := by decide

theorem final_root (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) (bottomMessage : Digest) :
    rootsAfter hash secretKey Heights 10 (GroupedMixedIndex.bottomTree index)
      bottomMessage = GroupedUpperTree.root hash secretKey 156 4 0 := by
  rw [heights_split, roots_after_append]
  simp only [prefix_height_sum, show 10 + 146 = 156 by decide, rootsAfter]
  change GroupedUpperTree.root hash secretKey 156 4
      (((index.toNat / 2 ^ 10) / 2 ^ 146) / 2 ^ 4) = _
  have hcap : 2 ^ 10 * (2 ^ 146 * 2 ^ 4) = 2 ^ 160 := by decide
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hcap]
  exact congrArg (GroupedUpperTree.root hash secretKey 156 4)
    (Nat.div_eq_of_lt index.isLt)

structure Signature where
  randomizer : Bytes 32
  bottom : GroupedBottomTree.Witness 10
  upper : UpperWitnesses Heights

def keygen (hash : Hash) (secretKey : SecretKey) : PublicKey :=
  GroupedUpperTree.root hash secretKey 156 4 0

def sign (hash : Hash) (secretKey : SecretKey) (message : Message) : Signature :=
  let randomizer := Reference.randomizer hash secretKey message
  let index := Reference.indexOf hash message randomizer
  let bottomTree := GroupedMixedIndex.bottomTree index
  let bottom := GroupedBottomTree.build hash secretKey 10 bottomTree index.toNat
  ⟨randomizer, bottom.witness,
    signLayers hash secretKey Heights 10 bottomTree bottom.root⟩

def verify (hash : Hash) (pk : PublicKey) (message : Message)
    (signature : Signature) : Prop :=
  let index := Reference.indexOf hash message signature.randomizer
  let bottomTree := GroupedMixedIndex.bottomTree index
  recoverLayers hash Heights 10 bottomTree
    (GroupedBottomTree.recover hash 10 bottomTree index.toNat signature.bottom)
    signature.upper = pk

theorem correct (hash : Hash) (secretKey : SecretKey) (message : Message) :
    verify hash (keygen hash secretKey) message (sign hash secretKey message) := by
  simp only [verify, sign, keygen]
  rw [GroupedBottomTree.recover_build, GroupedBottomTree.build_root,
    recover_sign_layers, final_root]

def Signature.encode (signature : Signature) : List Byte :=
  bytes signature.randomizer ++ signature.bottom.encode ++ signature.upper.encode

theorem signature_encode_injective : Function.Injective Signature.encode := by
  intro first second same
  simp only [Signature.encode, List.append_assoc] at same
  have randomizerBytes := List.append_inj_left same (by simp [bytes])
  have rest := List.append_inj_right same (by simp [bytes])
  have bottomLength :
      first.bottom.encode.length = second.bottom.encode.length := by
    rw [GroupedBottomTree.Witness.encode_length first.bottom,
      GroupedBottomTree.Witness.encode_length second.bottom]
  have bottomBytes := List.append_inj_left rest bottomLength
  have upperBytes := List.append_inj_right rest bottomLength
  have randomizerEq := SecurityPacking.bytes_injective 32 randomizerBytes
  have bottomEq := GroupedBottomTree.Witness.encode_injective bottomBytes
  have upperEq := UpperWitnesses.encode_injective upperBytes
  cases first
  cases second
  cases randomizerEq
  cases bottomEq
  cases upperEq
  rfl

theorem signature_bytes_length (signature : Signature) :
    signature.encode.length = 43376 := by
  simp only [Signature.encode, List.length_append]
  rw [GroupedBottomTree.Witness.encode_length signature.bottom,
    UpperWitnesses.encode_length signature.upper]
  rw [GroupedMixedIndex.upper_heights_length,
    GroupedMixedIndex.upper_heights_sum]
  simp [bytes]

end SigGolfCandidate.Hypertree.GroupedMixedScheme
