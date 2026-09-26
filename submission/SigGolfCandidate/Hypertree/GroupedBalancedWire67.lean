import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.SignatureDecode


/-! Parse every fixed-width bottom and upper witness field from a 50,848-byte
wire value. The encode equations show that the parser consumes each byte once. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedWireWitness67
open SigGolf SigGolfCandidate.Hypertree Reference SignatureEncoding
set_option maxRecDepth 8192

def bottomWitness (wire : Bytes 50848) :
    (height start : Nat) → GroupedBottomTree.Witness height
  | 0, start => .seed (slice wire start 16)
  | height + 1, start =>
      .step (bottomWitness wire height start)
        (slice wire (start + 16 * (height + 1)) 16)

theorem bottomWitness_encode (wire : Bytes 50848) (height start : Nat)
    (bound : start + 16 * (height + 1) ≤ 50848) :
    (bottomWitness wire height start).encode =
      ((bytes wire).drop start).take (16 * (height + 1)) := by
  induction height generalizing start with
  | zero =>
      simpa only [bottomWitness, GroupedBottomTree.Witness.encode, Nat.zero_add,
        Nat.mul_one] using bytes_slice wire start 16 (by omega)
  | succ height ih =>
      simp only [bottomWitness, GroupedBottomTree.Witness.encode]
      rw [ih start (by omega), bytes_slice wire (start + 16 * (height + 1)) 16 (by omega)]
      have take := (List.take_add (l := (bytes wire).drop start)
        (i := 16 * (height + 1)) (j := 16)).symm
      have count : 16 * (height + 1 + 1) = 16 * (height + 1) + 16 := by omega
      rw [count]
      simpa only [List.drop_drop] using take

def upperWitness (wire : Bytes 50848) :
    (height start : Nat) → GroupedBalancedUpperTree67.Witness height
  | 0, start => .leaf (fun chain => slice wire (start + 16 * chain.val) 16)
  | height + 1, start =>
      .step (upperWitness wire height start)
        (slice wire (start + 16 * (67 + height)) 16)

theorem upperWitness_encode (wire : Bytes 50848) (height start : Nat)
    (bound : start + 16 * (67 + height) ≤ 50848) :
    (upperWitness wire height start).encode =
      ((bytes wire).drop start).take (16 * (67 + height)) := by
  induction height generalizing start with
  | zero =>
      simp only [upperWitness, GroupedBalancedUpperTree67.Witness.encode]
      rw [ofFn_nat 67 (fun i => slice wire (start + 16 * i) 16),
        List.flatMap_map]
      rw [← chunks_reassemble (bytes wire) start 16 67]
      apply flatMap_eq_on
      intro i hi
      exact bytes_slice wire (start + 16 * i) 16 (by
        have : i < 67 := by simpa using hi
        omega)
  | succ height ih =>
      simp only [upperWitness, GroupedBalancedUpperTree67.Witness.encode]
      rw [ih start (by omega), bytes_slice wire (start + 16 * (67 + height)) 16 (by omega)]
      have take := (List.take_add (l := (bytes wire).drop start)
        (i := 16 * (67 + height)) (j := 16)).symm
      have count : 16 * (67 + (height + 1)) = 16 * (67 + height) + 16 := by omega
      rw [count]
      simpa only [List.drop_drop] using take

#print axioms bottomWitness_encode
#print axioms upperWitness_encode

end SigGolfCandidate.Hypertree.GroupedBalancedWireWitness67



/-! Every upper group consumes its exact 67-chain WOTS segment and its
authentication siblings. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedWireUpper67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedWireWitness67
set_option maxRecDepth 8192

def upperSize : List Nat → Nat
  | [] => 0
  | height :: rest => 16 * (67 + height) + upperSize rest

def upperList (wire : Bytes 50848) :
    (heights : List Nat) → (start : Nat) → UpperWitnesses heights
  | [], _ => .nil
  | height :: rest, start =>
      .cons (upperWitness wire height start)
        (upperList wire rest (start + 16 * (67 + height)))

theorem upperList_encode (wire : Bytes 50848) (heights : List Nat)
    (start : Nat) (bound : start + upperSize heights ≤ 50848) :
    (upperList wire heights start).encode =
      ((bytes wire).drop start).take (upperSize heights) := by
  induction heights generalizing start with
  | nil => simp [upperList, upperSize, UpperWitnesses.encode]
  | cons height rest ih =>
      simp only [upperList, UpperWitnesses.encode, upperSize]
      rw [upperWitness_encode wire height start (by
        simp only [upperSize] at bound
        omega)]
      rw [ih (start + 16 * (67 + height)) (by
        simp only [upperSize] at bound
        omega)]
      have take := (List.take_add (l := (bytes wire).drop start)
        (i := 16 * (67 + height)) (j := upperSize rest)).symm
      simpa only [List.drop_drop] using take

theorem upperSize_heights : upperSize Heights = 50640 := by decide

#print axioms upperList_encode

end SigGolfCandidate.Hypertree.GroupedBalancedWireUpper67


/-! Canonical conversion between the direct67 structured signature and the
organizer's fixed 50,848-byte wire type. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedWire67
open SigGolf SigGolfCandidate.Hypertree Reference SignatureEncoding
open GroupedBalancedScheme67 GroupedBalancedWireWitness67 GroupedBalancedWireUpper67
set_option maxRecDepth 8192

def decode (value : Bytes 50848) : GroupedBalancedScheme67.Signature where
  randomizer := slice value 0 32
  bottom := bottomWitness value 10 32
  upper := upperList value Heights 208

theorem decode_encode (value : Bytes 50848) :
    (decode value).encode = bytes value := by
  simp only [decode, GroupedBalancedScheme67.Signature.encode]
  rw [bytes_slice value 0 32 (by decide),
    bottomWitness_encode value 10 32 (by decide),
    upperList_encode value Heights 208 (by
      rw [upperSize_heights])]
  rw [upperSize_heights]
  simp only [show 16 * (10 + 1) = 176 by decide, List.drop_zero]
  rw [← List.take_add (l := bytes value) (i := 32) (j := 176)]
  have drop : 32 + 176 = 208 := by decide
  rw [drop]
  rw [← List.take_add (l := bytes value) (i := 208) (j := 50640)]
  apply List.take_of_length_le
  rw [Memory.bytes_length]

def wire (signature : GroupedBalancedScheme67.Signature) : Bytes 50848 :=
  (Reference.packed signature.encode).2.cast (by
    change 8 * signature.encode.length = 8 * 50848
    rw [GroupedBalancedScheme67.signature_bytes_length])

theorem wire_bytes (signature : GroupedBalancedScheme67.Signature) :
    bytes (wire signature) = signature.encode := by
  apply SecurityPacking.packed_injective
  rw [Serialization.packed_bytes]
  apply Serialization.query_eq
  · change 8 * 50848 = 8 * signature.encode.length
    rw [GroupedBalancedScheme67.signature_bytes_length]
  · simp only [wire, BitVec.toNat_cast]

theorem wire_decode (signature : GroupedBalancedScheme67.Signature) :
    decode (wire signature) = signature := by
  apply GroupedBalancedScheme67.signature_encode_injective
  rw [decode_encode, wire_bytes]

theorem decode_wire (value : Bytes 50848) :
    wire (decode value) = value := by
  apply SecurityPacking.bytes_injective 50848
  rw [wire_bytes, decode_encode]

#print axioms decode_wire
#print axioms wire_decode

end SigGolfCandidate.Hypertree.GroupedBalancedWire67
