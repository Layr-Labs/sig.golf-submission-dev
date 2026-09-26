import SigGolfCandidate.Hypertree.GroupedBalancedVerifyGenericPath67

/-! Witness digests survive decoder and verifier writes outside the wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem address_low (n : Nat) (bound : n < 0x80000) :
    (BitVec.ofNat 64 n).toNat < 0x80000 := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n < 2^64)]
  exact bound

theorem witness_digest_frame (s t : MachineState)
    (start height : Nat)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      t.getMem a = s.getMem a) (chain : Fin 67) :
    GroupedBalancedVerifyGenericPath67.witnessDigest t start chain =
      GroupedBalancedVerifyGenericPath67.witnessDigest s start chain := by
  have hc := chain.isLt
  have low0 : (BitVec.ofNat 64 (start+16*chain.val)).toNat <
      0x80000 := address_low _ (by omega)
  have low8 : (BitVec.ofNat 64 (start+16*chain.val+8)).toNat <
      0x80000 := address_low _ (by omega)
  simp only [GroupedBalancedVerifyGenericPath67.witnessDigest,
    frame _ low8,frame _ low0]

theorem sibling_digest_frame (s t : MachineState)
    (start height j : Nat)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (hj : j < height)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      t.getMem a = s.getMem a) :
    GroupedBalancedVerifyGenericPath67.siblingDigest t start j =
      GroupedBalancedVerifyGenericPath67.siblingDigest s start j := by
  have low0 : (BitVec.ofNat 64 (start+16*67+16*j)).toNat <
      0x80000 := address_low _ (by omega)
  have low8 : (BitVec.ofNat 64 (start+16*67+16*j+8)).toNat <
      0x80000 := address_low _ (by omega)
  simp only [GroupedBalancedVerifyGenericPath67.siblingDigest,
    frame _ low8,frame _ low0]

theorem rootAt_siblings_congr (hash : Hash)
    (base leaf : Nat) (initial : Reference.Digest)
    (left right : Nat → Reference.Digest) :
    ∀ h, (∀ j, j < h → left j = right j) →
      GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
        initial left h =
      GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
        initial right h := by
  intro h
  induction h with
  | zero => intro _; rfl
  | succ n ih =>
    intro same
    simp only [GroupedBalancedByteFastUpperPathIter67.rootAt]
    rw [ih (fun j hj => same j (by omega)),same n (by omega)]

theorem group_root_frame (hash : Hash) (s t : MachineState)
    (base leaf start height : Nat) (message : Reference.Digest)
    (wireBound : start + 16*67 + 16*height ≤ 0x38da0)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      t.getMem a = s.getMem a) :
    GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
      (GroupedBalancedUpperTree67.compressLeaf hash base leaf
        (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
          base leaf message
          (GroupedBalancedVerifyGenericPath67.witnessDigest t start)))
      (GroupedBalancedVerifyGenericPath67.siblingDigest t start) height =
    GroupedBalancedByteFastUpperPathIter67.rootAt hash base leaf
      (GroupedBalancedUpperTree67.compressLeaf hash base leaf
        (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
          base leaf message
          (GroupedBalancedVerifyGenericPath67.witnessDigest s start)))
      (GroupedBalancedVerifyGenericPath67.siblingDigest s start) height := by
  have sameWitness :
      GroupedBalancedVerifyGenericPath67.witnessDigest t start =
        GroupedBalancedVerifyGenericPath67.witnessDigest s start := by
    funext chain
    exact witness_digest_frame s t start height wireBound frame chain
  rw [sameWitness]
  exact rootAt_siblings_congr hash base leaf _ _ _ height
    (fun j hj => sibling_digest_frame s t start height j wireBound hj frame)

#print axioms group_root_frame
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireFrame67
