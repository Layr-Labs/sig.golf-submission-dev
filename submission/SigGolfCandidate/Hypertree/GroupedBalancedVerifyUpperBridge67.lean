import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedWire67

/-! Functional upper-tree recovery equals the machine path recurrence. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyUpperBridge67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def leafValues : {height : Nat} →
    GroupedBalancedUpperTree67.Witness height →
      (Fin 67 → Reference.Digest)
  | 0, .leaf values => values
  | _+1, .step inner _ => leafValues inner

def siblingAt : {height : Nat} →
    GroupedBalancedUpperTree67.Witness height →
      Nat → Reference.Digest
  | 0, .leaf _ => fun _ => 0
  | height+1, .step inner sibling =>
      fun j => if j < height then siblingAt inner j else sibling

theorem leafValues_upper (wire : Bytes 50848) (height start : Nat) :
    leafValues (GroupedBalancedWireWitness67.upperWitness wire height start) =
      (fun chain => SignatureEncoding.slice wire (start+16*chain.val) 16) := by
  induction height with
  | zero => rfl
  | succ height ih => exact ih

theorem siblingAt_upper (wire : Bytes 50848) (height start j : Nat)
    (hj : j < height) :
    siblingAt (GroupedBalancedWireWitness67.upperWitness wire height start) j =
      SignatureEncoding.slice wire (start+16*(67+j)) 16 := by
  induction height with
  | zero => omega
  | succ height ih =>
    simp only [GroupedBalancedWireWitness67.upperWitness,siblingAt]
    by_cases small : j < height
    · rw [if_pos small,ih small]
    · have eq : j = height := by omega
      rw [if_neg small,eq]

theorem recover_eq_rootAt (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest) :
    ∀ {height : Nat} (witness : GroupedBalancedUpperTree67.Witness height),
      GroupedBalancedUpperTree67.recover hash base height
        (leaf/2^height) leaf message witness =
      GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
        (GroupedBalancedUpperTree67.compressLeaf hash base leaf
          (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
            base leaf message (leafValues witness)))
        (siblingAt witness) height := by
  intro height witness
  induction witness with
  | leaf values =>
    simp only [GroupedBalancedUpperTree67.recover,
      GroupedBalancedByteFastUpperPathIter67.rootAt,
      leafValues,siblingAt,
      GroupedBalancedUpperTree67.recoverLeaf,
      GroupedBalancedByteFastEndpointAccum67.expectedEndpoint,
      pow_zero,Nat.div_one]
    rfl
  | @step height inner sibling ih =>
    have div_step : (leaf/2^height)/2 = leaf/2^(height+1) := by
      simp [pow_succ,Nat.div_div_eq_div_mul]
    have mod_div : leaf/2^height =
        2*(leaf/2^(height+1)) + (leaf/2^height)%2 := by
      have euclid := Nat.mod_add_div (leaf/2^height) 2
      omega
    have childRoot :
        GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
          (GroupedBalancedUpperTree67.compressLeaf hash base leaf
            (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
              base leaf message (leafValues inner)))
          (siblingAt (GroupedBalancedUpperTree67.Witness.step inner sibling))
          height =
        GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
          (GroupedBalancedUpperTree67.compressLeaf hash base leaf
            (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
              base leaf message (leafValues inner)))
          (siblingAt inner) height := by
      apply GroupedBalancedVerifyWireFrame67.rootAt_siblings_congr
      intro j hj
      simp [siblingAt,hj]
    simp only [siblingAt] at childRoot
    by_cases bit : (leaf/2^height)%2 = 0
    · have addr : 2*(leaf/2^(height+1)) = leaf/2^height := by
        omega
      simp only [GroupedBalancedUpperTree67.recover,if_pos bit,
        GroupedBalancedByteFastUpperPathIter67.rootAt,
        GroupedBalancedByteFastUpperPathIter67.indexAt,
        leafValues,siblingAt,if_neg (by omega : ¬ height < height)]
      rw [addr,ih,childRoot]
      simp only [GroupedBalancedByteFastEdgeNat67.nextRoot,if_pos bit]
      rw [div_step]
      rfl
    · have one : (leaf/2^height)%2 = 1 := by omega
      have addr : 2*(leaf/2^(height+1))+1 = leaf/2^height := by
        omega
      simp only [GroupedBalancedUpperTree67.recover,if_neg bit,
        GroupedBalancedByteFastUpperPathIter67.rootAt,
        GroupedBalancedByteFastUpperPathIter67.indexAt,
        leafValues,siblingAt,if_neg (by omega : ¬ height < height)]
      rw [addr,ih,childRoot]
      simp only [GroupedBalancedByteFastEdgeNat67.nextRoot,if_neg bit]
      rw [div_step]
      rfl

#print axioms recover_eq_rootAt
#print axioms leafValues_upper
#print axioms siblingAt_upper
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyUpperBridge67
