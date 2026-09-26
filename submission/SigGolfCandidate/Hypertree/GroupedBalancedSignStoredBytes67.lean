import SigGolfCandidate.Hypertree.GroupedBalancedSignLayersSchedule67
import SigGolfCandidate.Hypertree.SignWireBytes

/-! Turn selected 128-bit word pairs into stored bytes of a direct67 witness. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignStoredBytes67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree Reference SignatureEncoding
open GroupedBalancedUpperTree67 GroupedBalancedUpperBuildSibling67
open GroupedBalancedScheme67 GroupedBalancedSignWireUpperFields67
open GroupedBalancedWireUpper67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem digest_list_bytes (s : MachineState) (pointer : Nat)
    (values : List Digest) (aligned : pointer%8=0)
    (bound : pointer+16*values.length<2^64)
    (words : ∀ j (hj : j<values.length), ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (pointer+16*j+8*i.val)) =
        values[j].extractLsb' (64*i.val) 64) :
    SignWire.StoredBytes s pointer (values.flatMap bytes) := by
  induction values generalizing pointer with
  | nil =>
      intro i hi
      simp at hi
  | cons head tail ih =>
      have headWords : ∀ i : Fin 2,
          s.getMem (Signing.wordAddress pointer i.val) =
            head.extractLsb' (64*i.val) 64 := by
        intro i
        have h := words 0 (by simp) i
        change s.getMem (BitVec.ofNat 64 (pointer+8*i.val)) =
          head.extractLsb' (64*i.val) 64 at h
        simpa [Signing.wordAddress] using h
      have headBytes := SignWire.digest_bytes s pointer head aligned
        (by simp only [List.length_cons] at bound; omega) headWords
      have tailWords : ∀ j (hj : j<tail.length), ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64 ((pointer+16)+16*j+8*i.val)) =
            tail[j].extractLsb' (64*i.val) 64 := by
        intro j hj i
        have h := words (j+1) (by simp; omega) i
        simpa only [List.getElem_cons_succ,
          show pointer+16*(j+1)+8*i.val =
            (pointer+16)+16*j+8*i.val by omega] using h
      have tailBytes := ih (pointer+16) (by omega) (by
        simp only [List.length_cons] at bound
        omega) tailWords
      simpa only [List.flatMap_cons, Memory.bytes_length] using
        (SignWire.StoredBytes.append s pointer (bytes head)
          (tail.flatMap bytes) headBytes tailBytes)

theorem values_bytes (s : MachineState) (pointer : Nat)
    (values : ChainMixed → Digest) (aligned : pointer%8=0)
    (bound : pointer+16*67<2^64)
    (words : ∀ chain : ChainMixed, ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (pointer+16*chain.val+8*i.val)) =
        (values chain).extractLsb' (64*i.val) 64) :
    SignWire.StoredBytes s pointer ((List.ofFn values).flatMap bytes) := by
  apply digest_list_bytes s pointer (List.ofFn values) aligned
    (by simpa only [List.length_ofFn] using bound)
  intro j hj i
  simpa only [List.getElem_ofFn] using words ⟨j,by simpa only
    [List.length_ofFn] using hj⟩ i

theorem witness_bytes (s : MachineState) {height : Nat}
    (witness : Witness height) (pointer : Nat)
    (aligned : pointer%8=0)
    (bound : pointer+16*(67+height)<2^64)
    (leafWords : ∀ chain : ChainMixed, ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (pointer+16*chain.val+8*i.val)) =
        (GroupedBalancedUpperBuildSibling67.leafAt witness chain).extractLsb'
          (64*i.val) 64)
    (siblingWords : ∀ level, level<height → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (pointer+16*(67+level)+8*i.val)) =
        (GroupedBalancedUpperBuildSibling67.siblingAt witness level).extractLsb'
          (64*i.val) 64) :
    SignWire.StoredBytes s pointer witness.encode := by
  induction witness generalizing pointer with
  | leaf values =>
      change SignWire.StoredBytes s pointer
        ((List.ofFn values).flatMap bytes)
      apply values_bytes s pointer values aligned (by simpa using bound)
      intro chain i
      simpa only [GroupedBalancedUpperBuildSibling67.leafAt] using
        leafWords chain i
  | @step height inner sibling ih =>
      have innerLeaf : ∀ chain : ChainMixed, ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64 (pointer+16*chain.val+8*i.val)) =
            (GroupedBalancedUpperBuildSibling67.leafAt inner chain).extractLsb'
              (64*i.val) 64 := by
        intro chain i
        simpa only [GroupedBalancedUpperBuildSibling67.leafAt] using
          leafWords chain i
      have innerSiblings : ∀ level, level<height → ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64 (pointer+16*(67+level)+8*i.val)) =
            (GroupedBalancedUpperBuildSibling67.siblingAt inner level).extractLsb'
              (64*i.val) 64 := by
        intro level lt i
        have source := siblingWords level (by omega) i
        simpa only [GroupedBalancedUpperBuildSibling67.siblingAt,
          if_neg (by omega : level ≠ height)] using source
      have innerBytes := ih pointer aligned (by omega) innerLeaf innerSiblings
      have siblingAtPointer : ∀ i : Fin 2,
          s.getMem (Signing.wordAddress
            (pointer+16*(67+height)) i.val) =
            sibling.extractLsb' (64*i.val) 64 := by
        intro i
        have h := siblingWords height (by omega) i
        simpa [Signing.wordAddress,
          GroupedBalancedUpperBuildSibling67.siblingAt] using h
      have siblingBytes := SignWire.digest_bytes s
        (pointer+16*(67+height)) sibling (by omega) (by omega)
        siblingAtPointer
      change SignWire.StoredBytes s pointer (inner.encode ++ bytes sibling)
      have address : pointer+inner.encode.length =
          pointer+16*(67+height) := by
        rw [Witness.encode_length inner]
        omega
      have joined := SignWire.StoredBytes.append s pointer
        inner.encode (bytes sibling) innerBytes (by
          simpa only [address] using siblingBytes)
      exact joined

theorem upper_bytes (s : MachineState) {heights : List Nat}
    (witnesses : UpperWitnesses heights) (pointer : Nat)
    (aligned : pointer%8=0)
    (bound : pointer+upperSize heights<2^64)
    (leafWords : ∀ k (hk : k<heights.length),
      ∀ chain : ChainMixed, ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64
        (pointer+upperSize (heights.take k)+16*chain.val+8*i.val)) =
        (GroupedBalancedSignWireUpperFields67.leafAt witnesses k chain).extractLsb'
          (64*i.val) 64)
    (siblingWords : ∀ k (hk : k<heights.length),
      ∀ level, level<heights[k]'hk → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64
        (pointer+upperSize (heights.take k)+16*(67+level)+8*i.val)) =
        (GroupedBalancedSignWireUpperFields67.siblingAt witnesses k level).extractLsb'
          (64*i.val) 64) :
    SignWire.StoredBytes s pointer witnesses.encode := by
  induction witnesses generalizing pointer with
  | nil =>
      intro i hi
      simp [UpperWitnesses.encode] at hi
  | @cons height rest head tail ih =>
      have headLeaf : ∀ chain : ChainMixed, ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64
            (pointer+16*chain.val+8*i.val)) =
            (GroupedBalancedUpperBuildSibling67.leafAt head chain).extractLsb'
              (64*i.val) 64 := by
        intro chain i
        simpa only [List.take_zero, upperSize, Nat.add_zero,
          GroupedBalancedSignWireUpperFields67.leafAt] using
          leafWords 0 (by simp) chain i
      have headSibling : ∀ level, level<height → ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64
            (pointer+16*(67+level)+8*i.val)) =
            (GroupedBalancedUpperBuildSibling67.siblingAt head level).extractLsb'
              (64*i.val) 64 := by
        intro level lt i
        simpa only [List.take_zero, upperSize, Nat.add_zero,
          GroupedBalancedSignWireUpperFields67.siblingAt,
          List.getElem_cons_zero] using
          siblingWords 0 (by simp) level lt i
      have headBytes := witness_bytes s head pointer aligned
        (by simp only [upperSize] at bound; omega) headLeaf headSibling
      have tailLeaf : ∀ k (hk : k<rest.length),
          ∀ chain : ChainMixed, ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64
            ((pointer+16*(67+height))+upperSize (rest.take k)+
              16*chain.val+8*i.val)) =
            (GroupedBalancedSignWireUpperFields67.leafAt tail k chain).extractLsb'
              (64*i.val) 64 := by
        intro k hk chain i
        have source := leafWords (k+1) (by simp; omega) chain i
        simpa only [List.take_succ_cons, upperSize,
          GroupedBalancedSignWireUpperFields67.leafAt,
          Nat.add_assoc] using source
      have tailSibling : ∀ k (hk : k<rest.length),
          ∀ level, level<rest[k]'hk → ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64
            ((pointer+16*(67+height))+upperSize (rest.take k)+
              16*(67+level)+8*i.val)) =
            (GroupedBalancedSignWireUpperFields67.siblingAt tail k level).extractLsb'
              (64*i.val) 64 := by
        intro k hk level lt i
        have source := siblingWords (k+1) (by simp; omega)
          level (by simpa only [List.getElem_cons_succ] using lt) i
        simpa only [List.take_succ_cons, upperSize,
          GroupedBalancedSignWireUpperFields67.siblingAt,
          Nat.add_assoc] using source
      have tailBytes := ih (pointer+16*(67+height)) (by omega)
        (by simp only [upperSize] at bound; omega) tailLeaf tailSibling
      change SignWire.StoredBytes s pointer
        (head.encode ++ tail.encode)
      have address : pointer+head.encode.length =
          pointer+16*(67+height) := by
        rw [Witness.encode_length head]
        omega
      exact SignWire.StoredBytes.append s pointer head.encode
        tail.encode headBytes (by simpa only [address] using tailBytes)

theorem bottom_bytes (s : MachineState) {height : Nat}
    (witness : GroupedBottomTree.Witness height) (pointer : Nat)
    (aligned : pointer%8=0)
    (bound : pointer+16*(height+1)<2^64)
    (seedWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress pointer i.val) =
        witness.seedValue.extractLsb' (64*i.val) 64)
    (siblingWords : ∀ level, level<height → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (pointer+16*(level+1)+8*i.val)) =
        (GroupedBalancedBottomBuildSibling67.siblingAt witness level).extractLsb'
          (64*i.val) 64) :
    SignWire.StoredBytes s pointer witness.encode := by
  induction witness generalizing pointer with
  | seed value =>
      change SignWire.StoredBytes s pointer (bytes value)
      exact SignWire.digest_bytes s pointer value aligned (by omega)
        (by simpa only [GroupedBottomTree.Witness.seedValue] using seedWords)
  | @step height inner sibling ih =>
      have innerSeed : ∀ i : Fin 2,
          s.getMem (Signing.wordAddress pointer i.val) =
            inner.seedValue.extractLsb' (64*i.val) 64 := by
        simpa only [GroupedBottomTree.Witness.seedValue] using seedWords
      have innerSiblings : ∀ level, level<height → ∀ i : Fin 2,
          s.getMem (BitVec.ofNat 64 (pointer+16*(level+1)+8*i.val)) =
            (GroupedBalancedBottomBuildSibling67.siblingAt inner level).extractLsb'
              (64*i.val) 64 := by
        intro level lt i
        have source := siblingWords level (by omega) i
        simpa only [GroupedBalancedBottomBuildSibling67.siblingAt,
          if_neg (by omega : level ≠ height)] using source
      have innerBytes := ih pointer aligned (by omega) innerSeed innerSiblings
      have siblingAtPointer : ∀ i : Fin 2,
          s.getMem (Signing.wordAddress (pointer+16*(height+1)) i.val) =
            sibling.extractLsb' (64*i.val) 64 := by
        intro i
        have h := siblingWords height (by omega) i
        simpa [Signing.wordAddress,
          GroupedBalancedBottomBuildSibling67.siblingAt] using h
      have siblingBytes := SignWire.digest_bytes s
        (pointer+16*(height+1)) sibling (by omega) (by omega)
        siblingAtPointer
      change SignWire.StoredBytes s pointer (inner.encode ++ bytes sibling)
      have address : pointer+inner.encode.length =
          pointer+16*(height+1) := by
        rw [GroupedBottomTree.Witness.encode_length inner]
        omega
      exact SignWire.StoredBytes.append s pointer inner.encode
        (bytes sibling) innerBytes (by simpa only [address] using siblingBytes)

theorem read_signature (s : MachineState)
    (signature : GroupedBalancedScheme67.Signature)
    (randomWords : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20060 i.val) =
        signature.randomizer.extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x20080 i.val) =
        signature.bottom.seedValue.extractLsb' (64*i.val) 64)
    (bottomSiblings : ∀ level, level<10 → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x20080+16*(level+1)+8*i.val)) =
        (GroupedBalancedBottomBuildSibling67.siblingAt
          signature.bottom level).extractLsb' (64*i.val) 64)
    (upperLeaves : ∀ k (hk : k<Heights.length),
      ∀ chain : ChainMixed, ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64
        (0x20130+upperSize (Heights.take k)+16*chain.val+8*i.val)) =
        (GroupedBalancedSignWireUpperFields67.leafAt
          signature.upper k chain).extractLsb' (64*i.val) 64)
    (upperSiblings : ∀ k (hk : k<Heights.length),
      ∀ level, level<Heights[k]'hk → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64
        (0x20130+upperSize (Heights.take k)+16*(67+level)+8*i.val)) =
        (GroupedBalancedSignWireUpperFields67.siblingAt
          signature.upper k level).extractLsb' (64*i.val) 64) :
    readBuffer s 0x20060 50848 = GroupedBalancedWire67.wire signature := by
  have randomBytes : SignWire.StoredBytes s 0x20060
      (bytes signature.randomizer) :=
    SignWire.words_bytes s 0x20060 signature.randomizer (by decide)
      (by decide) (by
        intro i hi
        exact randomWords ⟨i,by omega⟩)
  have bottomBytes : SignWire.StoredBytes s 0x20080
      signature.bottom.encode :=
    bottom_bytes s signature.bottom 0x20080 (by decide) (by decide)
      seedWords bottomSiblings
  have upperBytes : SignWire.StoredBytes s 0x20130
      signature.upper.encode :=
    upper_bytes s signature.upper 0x20130 (by decide) (by
      rw [upperSize_heights]
      decide) upperLeaves upperSiblings
  have tailBytes : SignWire.StoredBytes s 0x20080
      (signature.bottom.encode ++ signature.upper.encode) := by
    apply SignWire.StoredBytes.append s 0x20080
      signature.bottom.encode signature.upper.encode bottomBytes
    have len : signature.bottom.encode.length=176 := by
      rw [GroupedBottomTree.Witness.encode_length]
    simpa only [len] using upperBytes
  have fullBytes : SignWire.StoredBytes s 0x20060 signature.encode := by
    have joined := SignWire.StoredBytes.append s 0x20060
      (bytes signature.randomizer)
      (signature.bottom.encode ++ signature.upper.encode)
      randomBytes (by
        simpa only [Memory.bytes_length] using tailBytes)
    simpa only [GroupedBalancedScheme67.Signature.encode,
      List.append_assoc] using joined
  apply Memory.readBuffer_of_bytes
  intro i hi
  have stored := fullBytes i (by
    rw [←GroupedBalancedWire67.wire_bytes signature]
    simpa only [Memory.bytes_length] using hi)
  simpa only [←GroupedBalancedWire67.wire_bytes signature,
    bytes, List.getElem_map, List.getElem_range] using stored

#print axioms digest_list_bytes
#print axioms values_bytes
#print axioms witness_bytes
#print axioms upper_bytes
#print axioms bottom_bytes
#print axioms read_signature
end SigGolfCandidate.Hypertree.GroupedBalancedSignStoredBytes67
