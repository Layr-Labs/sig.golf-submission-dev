import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Hypertree.GroupedBalancedBottomBuildSibling67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperBuildSibling67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSchedule67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignWireFields67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignWireUpperFields67. -/
section
/-! The canonical wire exposes exactly the randomizer and bottom witness words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignWireFields67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedWire67
open GroupedBalancedWireWitness67 GroupedBalancedBottomBuildSibling67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem slice_word {n : Nat} (value : Bytes n)
    (start : Nat) (i : Fin 2) :
    (SignatureEncoding.slice value start 16).extractLsb' (64*i.val) 64 =
      value.extractLsb' (8*start+64*i.val) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have inner : 64*i.val+j < 128 := by have := i.isLt; omega
  simp only [SignatureEncoding.slice, BitVec.getLsbD_extractLsb']
  simp only [hj, inner, decide_true, Bool.true_and, Nat.add_assoc]

theorem randomizer_word (signature : GroupedBalancedScheme67.Signature) (i : Fin 4) :
    (wire signature).extractLsb' (64*i.val) 64 =
      signature.randomizer.extractLsb' (64*i.val) 64 := by
  have decodeEq := wire_decode signature
  have randomizerEq := congrArg GroupedBalancedScheme67.Signature.randomizer decodeEq
  change (wire signature).extractLsb' 0 256 = signature.randomizer at randomizerEq
  have bound : 64*i.val + 64 ≤ 256 := by have := i.isLt; omega
  rw [← BitVec.extractLsb'_extractLsb'_of_le (x := wire signature) bound,
    randomizerEq]

private theorem bottomWitness_seed (value : Bytes 50848)
    (height start : Nat) :
    (bottomWitness value height start).seedValue =
      SignatureEncoding.slice value start 16 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simpa only [bottomWitness, GroupedBottomTree.Witness.seedValue] using ih

private theorem bottomWitness_sibling (value : Bytes 50848)
    (height start level : Nat) (lt : level < height) :
    siblingAt (bottomWitness value height start) level =
      SignatureEncoding.slice value (start + 16*(level+1)) 16 := by
  induction height with
  | zero => omega
  | succ height ih =>
      by_cases top : level = height
      · subst level
        simp only [bottomWitness, siblingAt, ite_true]
      · have low : level < height := by omega
        simp only [bottomWitness, siblingAt, if_neg top]
        exact ih low

theorem bottom_seed_word (signature : GroupedBalancedScheme67.Signature) (i : Fin 2) :
    (wire signature).extractLsb' (256+64*i.val) 64 =
      signature.bottom.seedValue.extractLsb' (64*i.val) 64 := by
  have decodeEq := wire_decode signature
  have bottomEq := congrArg GroupedBalancedScheme67.Signature.bottom decodeEq
  have seedEq := congrArg (GroupedBottomTree.Witness.seedValue (height := 10)) bottomEq
  change (bottomWitness (wire signature) 10 32).seedValue =
    signature.bottom.seedValue at seedEq
  rw [bottomWitness_seed] at seedEq
  rw [← slice_word (wire signature) 32 i, seedEq]

theorem bottom_sibling_word (signature : GroupedBalancedScheme67.Signature)
    (level : Nat) (lt : level < 10) (i : Fin 2) :
    (wire signature).extractLsb' (8*(32+16*(level+1))+64*i.val) 64 =
      (siblingAt signature.bottom level).extractLsb' (64*i.val) 64 := by
  have decodeEq := wire_decode signature
  have bottomEq := congrArg GroupedBalancedScheme67.Signature.bottom decodeEq
  have siblingEq := congrArg (fun w : GroupedBottomTree.Witness 10 =>
      siblingAt w level) bottomEq
  change siblingAt (bottomWitness (wire signature) 10 32) level =
    siblingAt signature.bottom level at siblingEq
  rw [bottomWitness_sibling (wire signature) 10 32 level lt] at siblingEq
  rw [← slice_word (wire signature) (32+16*(level+1)) i, siblingEq]

theorem signed_randomizer_word (hash : Hash) (secretKey : SecretKey)
    (message : Message) (i : Fin 4) :
    (wire (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb' (64*i.val) 64 =
      (Reference.randomizer hash secretKey message).extractLsb'
        (64*i.val) 64 := by
  rw [randomizer_word]
  rfl

theorem signed_bottom_seed_word (hash : Hash) (secretKey : SecretKey)
    (message : Message) (i : Fin 2) :
    (wire (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb'
      (256+64*i.val) 64 =
      (GroupedBottomTree.secret hash secretKey
        (Reference.indexOf hash message
          (Reference.randomizer hash secretKey message)).toNat).extractLsb'
          (64*i.val) 64 := by
  rw [bottom_seed_word]
  let index := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  change ((GroupedBottomTree.build hash secretKey 10
    (index.toNat / 2^10) index.toNat).witness.seedValue).extractLsb'
      (64*i.val) 64 = _
  rw [GroupedBottomTree.build_seed_at_full_index]

theorem signed_bottom_sibling_word (hash : Hash) (secretKey : SecretKey)
    (message : Message) (level : Nat) (lt : level < 10) (i : Fin 2) :
    (wire (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb'
      (8*(32+16*(level+1))+64*i.val) 64 =
      (GroupedBottomTree.root hash secretKey level
        (if (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat / 2^level % 2 = 0
          then (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat / 2^level + 1
          else (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat / 2^level - 1)).extractLsb'
              (64*i.val) 64 := by
  rw [bottom_sibling_word (GroupedBalancedScheme67.sign hash secretKey message)
    level lt i]
  let index := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  change (siblingAt (GroupedBottomTree.build hash secretKey 10
    (index.toNat / 2^10) index.toNat).witness level).extractLsb'
      (64*i.val) 64 = _
  rw [GroupedBalancedBottomBuildSibling67.build_sibling hash secretKey
    10 index.toNat level lt]

#print axioms randomizer_word
#print axioms bottom_seed_word
#print axioms bottom_sibling_word
#print axioms signed_randomizer_word
#print axioms signed_bottom_seed_word
#print axioms signed_bottom_sibling_word
end SigGolfCandidate.Hypertree.GroupedBalancedSignWireFields67

end

/-! Locate each upper WOTS and authentication word in the canonical wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignWireUpperFields67
open SigGolf SigGolfCandidate.Hypertree Reference SignatureEncoding
open GroupedBalancedScheme67 GroupedBalancedWire67
open GroupedBalancedWireWitness67 GroupedBalancedWireUpper67
open GroupedBalancedUpperBuildSibling67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def leafAt : {heights : List Nat} → UpperWitnesses heights → Nat →
    GroupedBalancedUpperTree67.ChainMixed → Digest
  | [], .nil, _, _ => 0
  | _ :: _, .cons head _, 0, chain =>
      GroupedBalancedUpperBuildSibling67.leafAt head chain
  | _ :: _, .cons _ tail, k+1, chain => leafAt tail k chain

def siblingAt : {heights : List Nat} → UpperWitnesses heights → Nat → Nat → Digest
  | [], .nil, _, _ => 0
  | _ :: _, .cons head _, 0, level =>
      GroupedBalancedUpperBuildSibling67.siblingAt head level
  | _ :: _, .cons _ tail, k+1, level => siblingAt tail k level

private theorem upperWitness_leaf (value : Bytes 50848)
    (height start : Nat) (chain : GroupedBalancedUpperTree67.ChainMixed) :
    GroupedBalancedUpperBuildSibling67.leafAt
      (upperWitness value height start) chain =
      slice value (start+16*chain.val) 16 := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simpa only [upperWitness,
        GroupedBalancedUpperBuildSibling67.leafAt] using ih

private theorem upperWitness_sibling (value : Bytes 50848)
    (height start level : Nat) (lt : level < height) :
    GroupedBalancedUpperBuildSibling67.siblingAt
      (upperWitness value height start) level =
      slice value (start+16*(67+level)) 16 := by
  induction height with
  | zero => omega
  | succ height ih =>
      by_cases top : level=height
      · subst level
        simp only [upperWitness,
          GroupedBalancedUpperBuildSibling67.siblingAt, ite_true]
      · have low : level<height := by omega
        simp only [upperWitness,
          GroupedBalancedUpperBuildSibling67.siblingAt, if_neg top]
        exact ih low

theorem upperList_leaf (value : Bytes 50848) (heights : List Nat)
    (start k : Nat) (hk : k < heights.length)
    (chain : GroupedBalancedUpperTree67.ChainMixed) :
    leafAt (upperList value heights start) k chain =
      slice value (start+upperSize (heights.take k)+16*chain.val) 16 := by
  induction heights generalizing start k with
  | nil => simp at hk
  | cons height rest ih =>
      cases k with
      | zero =>
          simpa only [upperList, leafAt, List.take_zero, upperSize,
            Nat.add_zero] using upperWitness_leaf value height start chain
      | succ k =>
          have low : k<rest.length := by simpa using hk
          simpa only [upperList, leafAt, List.take_succ_cons,
            upperSize, Nat.add_assoc] using
            ih (start+16*(67+height)) k low

theorem upperList_sibling (value : Bytes 50848) (heights : List Nat)
    (start k level : Nat) (hk : k < heights.length)
    (lt : level < heights[k]'hk) :
    siblingAt (upperList value heights start) k level =
      slice value (start+upperSize (heights.take k)+16*(67+level)) 16 := by
  induction heights generalizing start k with
  | nil => simp at hk
  | cons height rest ih =>
      cases k with
      | zero =>
          simpa only [upperList, siblingAt, List.take_zero, upperSize,
            Nat.add_zero, List.getElem_cons_zero] using
            upperWitness_sibling value height start level lt
      | succ k =>
          have low : k<rest.length := by simpa using hk
          simpa only [upperList, siblingAt, List.take_succ_cons,
            upperSize, Nat.add_assoc, List.getElem_cons_succ] using
            ih (start+16*(67+height)) k low lt

theorem upperSize_formula (heights : List Nat) :
    upperSize heights = 16*(67*heights.length+heights.sum) := by
  induction heights with
  | nil => simp [upperSize]
  | cons height rest ih =>
      simp only [upperSize, ih, List.length_cons, List.sum_cons]
      omega

theorem fixed_heights (k : Nat) (hk : k < 45) :
    Heights[k]? =
      some (GroupedBalancedSignUpperSchedule67.height k) := by
  interval_cases k <;> decide

theorem fixed_prefix (k : Nat) (hk : k ≤ 45) :
    (Heights.take k).sum =
      GroupedBalancedSignUpperSchedule67.prefixHeight k := by
  interval_cases k <;> decide

theorem wire_upper_start (k : Nat) (hk : k ≤ 45) :
    0x20060 + 208 + upperSize (Heights.take k) =
      GroupedBalancedSignUpperSchedule67.currentWitness k := by
  rw [upperSize_formula]
  have length : (Heights.take k).length = k := by
    rw [List.length_take, GroupedBalancedScheme67.heights_length]
    omega
  rw [length, fixed_prefix k hk]
  unfold GroupedBalancedSignUpperSchedule67.currentWitness
  omega

theorem wire_upper_leaf_word
    (signature : GroupedBalancedScheme67.Signature)
    (k : Nat) (hk : k < Heights.length)
    (chain : GroupedBalancedUpperTree67.ChainMixed) (i : Fin 2) :
    (wire signature).extractLsb'
      (8*(208+upperSize (Heights.take k)+16*chain.val)+64*i.val) 64 =
      (leafAt signature.upper k chain).extractLsb' (64*i.val) 64 := by
  have decoded := wire_decode signature
  have upperEq := congrArg GroupedBalancedScheme67.Signature.upper decoded
  change upperList (wire signature) Heights 208 = signature.upper at upperEq
  have leafEq := congrArg (fun w : UpperWitnesses Heights =>
      leafAt w k chain) upperEq
  rw [upperList_leaf (wire signature) Heights 208 k hk chain] at leafEq
  rw [← GroupedBalancedSignWireFields67.slice_word
    (wire signature) (208+upperSize (Heights.take k)+16*chain.val) i,
    leafEq]

theorem wire_upper_sibling_word
    (signature : GroupedBalancedScheme67.Signature)
    (k : Nat) (hk : k < Heights.length)
    (level : Nat) (lt : level < Heights[k]'hk) (i : Fin 2) :
    (wire signature).extractLsb'
      (8*(208+upperSize (Heights.take k)+16*(67+level))+64*i.val) 64 =
      (siblingAt signature.upper k level).extractLsb' (64*i.val) 64 := by
  have decoded := wire_decode signature
  have upperEq := congrArg GroupedBalancedScheme67.Signature.upper decoded
  change upperList (wire signature) Heights 208 = signature.upper at upperEq
  have siblingEq := congrArg (fun w : UpperWitnesses Heights =>
      siblingAt w k level) upperEq
  rw [upperList_sibling (wire signature) Heights 208 k level hk lt] at siblingEq
  rw [← GroupedBalancedSignWireFields67.slice_word
    (wire signature) (208+upperSize (Heights.take k)+16*(67+level)) i,
    siblingEq]

#print axioms upperList_leaf
#print axioms upperList_sibling
#print axioms upperSize_formula
#print axioms fixed_heights
#print axioms fixed_prefix
#print axioms wire_upper_start
#print axioms wire_upper_leaf_word
#print axioms wire_upper_sibling_word
end SigGolfCandidate.Hypertree.GroupedBalancedSignWireUpperFields67
