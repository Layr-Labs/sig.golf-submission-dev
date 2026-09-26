import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
import SigGolfCandidate.Hypertree.SecurityVerifyCost

/-! Exact public-oracle query count of the direct67 reference verifier. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyCallBridge67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec Reference
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.SecurityVerifyCost
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem calls_bottomLeaf (hash : Hash) (address : Nat)
    (seed : Reference.Digest) :
    calls hash (GroupedBalancedVerifyOracle67.bottomLeaf address seed) = 1 := by
  simp [GroupedBalancedVerifyOracle67.bottomLeaf]

theorem calls_node (hash : Hash) (level address : Nat)
    (left right : Reference.Digest) :
    calls hash (GroupedBalancedVerifyOracle67.node level address left right) = 1 := by
  simp [GroupedBalancedVerifyOracle67.node]

theorem calls_recoverBottom (hash : Hash) (height address index : Nat)
    (witness : GroupedBottomTree.Witness height) :
    calls hash (GroupedBalancedVerifyOracle67.recoverBottom height address index witness) = height+1 := by
  induction witness generalizing address index with
  | seed seed => exact calls_bottomLeaf hash address seed
  | @step height inner sibling ih =>
    by_cases bit : index/2^height%2=0
    · simp only [GroupedBalancedVerifyOracle67.recoverBottom,if_pos bit,calls_bind,ih,calls_node]
    · simp only [GroupedBalancedVerifyOracle67.recoverBottom,if_neg bit,calls_bind,ih,calls_node]

theorem calls_walk_one (hash : Hash)
    (body : Nat → Reference.Digest → OracleComp HashSpec Reference.Digest)
    (one : ∀ step value, calls hash (body step value) = 1)
    (start count : Nat) (value : Reference.Digest) :
    calls hash (SecurityReference.walk body start count value) = count := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    simp only [SecurityReference.walk,calls_bind]
    rw [one start value,ih]
    omega

theorem calls_chainHash (hash : Hash) (base leaf : Nat)
    (chain : Fin 67) (step : Nat) (value : Reference.Digest) :
    calls hash (GroupedBalancedVerifyOracle67.chainHash base leaf chain step value) = 1 := by
  simp [GroupedBalancedVerifyOracle67.chainHash]

theorem calls_compressLeaf (hash : Hash) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest) :
    calls hash (GroupedBalancedVerifyOracle67.compressLeaf base leaf values) = 1 := by
  simp [GroupedBalancedVerifyOracle67.compressLeaf]

theorem calls_recoverLeaf (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest) (values : Fin 67 → Reference.Digest) :
    calls hash (GroupedBalancedVerifyOracle67.recoverLeaf base leaf message values) =
      GroupedBalancedChecksum67.suffixCost message+1 := by
  simp only [GroupedBalancedVerifyOracle67.recoverLeaf,calls_bind,calls_compressLeaf,
    calls_sequenceFin]
  have each (i : Fin 67) :
      calls hash
        (SecurityReference.walk
          (GroupedBalancedVerifyOracle67.chainHash base leaf i)
          (GroupedBalancedUpperTree67.digit message i).val
          (GroupedBalancedUpperTree67.maxDigit i -
            (GroupedBalancedUpperTree67.digit message i).val)
          (values i)) =
      GroupedBalancedChecksum67.maxDigit i-
        (GroupedBalancedChecksum67.digit message i).val :=
    calls_walk_one hash _ (calls_chainHash hash base leaf i) _ _ _
  simp only [each,GroupedBalancedChecksum67.suffixCost]

theorem calls_recoverUpper (hash : Hash) (base height address index : Nat)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height) :
    calls hash (GroupedBalancedVerifyOracle67.recoverUpper base height address index message witness) =
      GroupedBalancedChecksum67.suffixCost message+1+height := by
  induction witness generalizing address index with
  | leaf values => exact calls_recoverLeaf hash base address message values
  | @step height inner sibling ih =>
    by_cases bit : index/2^height%2=0
    · simp only [GroupedBalancedVerifyOracle67.recoverUpper,if_pos bit,calls_bind,ih,calls_node]
      omega
    · simp only [GroupedBalancedVerifyOracle67.recoverUpper,if_neg bit,calls_bind,ih,calls_node]
      omega

def layersCalls (hash : Hash) :
    (heights : List Nat) → (base index : Nat) → Reference.Digest →
      GroupedBalancedScheme67.UpperWitnesses heights → Nat
  | [], _, _, _, .nil => 0
  | height :: rest, base, index, root, .cons head tail =>
      let tree := index/2^height
      GroupedBalancedChecksum67.suffixCost root+1+height+
        layersCalls hash rest (base+height) tree
          (GroupedBalancedUpperTree67.recover hash base height tree index
            root head) tail

theorem calls_recoverLayers (hash : Hash) (heights : List Nat)
    (base index : Nat) (root : Reference.Digest)
    (witnesses : GroupedBalancedScheme67.UpperWitnesses heights) :
    calls hash (GroupedBalancedVerifyOracle67.recoverLayers heights base index root witnesses) =
      layersCalls hash heights base index root witnesses := by
  induction witnesses generalizing base index root with
  | nil => rfl
  | @cons height rest head tail ih =>
    simp only [GroupedBalancedVerifyOracle67.recoverLayers,calls_bind,calls_recoverUpper,
      GroupedBalancedVerifyOracle67.eval_recoverUpper,ih,layersCalls]

theorem calls_verify (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) :
    let index := Reference.indexOf hash message signature.randomizer
    let bottomTree := GroupedMixedIndex.bottomTree index
    calls hash (GroupedBalancedVerifyOracle67.verify pk message signature) =
      12+layersCalls hash GroupedBalancedScheme67.Heights 10 bottomTree
        (GroupedBottomTree.recover hash 10 bottomTree index.toNat signature.bottom)
        signature.upper := by
  simp only [GroupedBalancedVerifyOracle67.verify,calls_bind,
    calls_recoverBottom,calls_recoverLayers,
    GroupedBalancedVerifyOracle67.eval_recoverBottom,
    SecurityReference.eval_ask,Reference.indexOf]
  simp only [calls_ask,calls_pure]
  omega

def wireLayersCalls (hash : Hash) (wire : Bytes 50848) :
    (heights : List Nat) → (base index start : Nat) → Digest → Nat
  | [], _, _, _, _ => 0
  | height :: rest, base, index, start, root =>
      let tree := index/2^height
      GroupedBalancedChecksum67.suffixCost root+1+height+
        wireLayersCalls hash wire rest (base+height) tree
          (start+16*(67+height))
          (GroupedBalancedUpperTree67.recover hash base height tree index root
            (GroupedBalancedWireWitness67.upperWitness wire height start))

theorem layersCalls_wire (hash : Hash) (wire : Bytes 50848)
    (heights : List Nat) (base index start : Nat) (root : Digest) :
    layersCalls hash heights base index root
      (GroupedBalancedWireUpper67.upperList wire heights start) =
    wireLayersCalls hash wire heights base index start root := by
  induction heights generalizing base index start root with
  | nil => rfl
  | cons height rest ih =>
    simp only [layersCalls,GroupedBalancedWireUpper67.upperList,
      wireLayersCalls]
    rw [ih]

theorem calls_prefix (hash : Hash) (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (leaf0 g : Nat) (hg : g ≤ 45) :
    wireLayersCalls hash wire GroupedBalancedScheme67.Heights 10 leaf0 208
      (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry) =
    GroupedBalancedVerifyGroupFold67.callsAt hash entry leaf0 g +
      wireLayersCalls hash wire (GroupedBalancedScheme67.Heights.drop g)
        (GroupedBalancedVerifyGroupFold67.baseAt g)
        (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g)
        (GroupedBalancedVerifyLoadedWire67.offsetAt g)
        (GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 g) := by
  induction g with
  | zero =>
      simp only [List.drop_zero,
        GroupedBalancedVerifyGroupFold67.base_zero,
        GroupedBalancedVerifyGroupFold67.leaf_zero,
        GroupedBalancedVerifyGroupFold67.rootAt,
        GroupedBalancedVerifyGroupFold67.callsAt,
        GroupedBalancedVerifyLoadedWire67.offsetAt,
        GroupedBalancedVerifyGroupFold67.accumulated_zero,
        Nat.mul_zero,Nat.add_zero,zero_add]
  | succ g ih =>
      have small : g < 45 := by omega
      have prev := ih (by omega)
      rw [GroupedBalancedVerifyLoadedWire67.heights_drop_step g small] at prev
      simp only [wireLayersCalls] at prev
      have nextRoot :
          GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 (g+1) =
          GroupedBalancedUpperTree67.recover hash
            (GroupedBalancedVerifyGroupFold67.baseAt g)
            (GroupedBalancedVerifyGroupFold67.heightAt g)
            (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g /
              2^GroupedBalancedVerifyGroupFold67.heightAt g)
            (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g)
            (GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 g)
            (GroupedBalancedWireWitness67.upperWitness wire
              (GroupedBalancedVerifyGroupFold67.heightAt g)
              (GroupedBalancedVerifyLoadedWire67.offsetAt g)) := by
        simpa only [GroupedBalancedVerifyGroupFold67.rootAt] using
          GroupedBalancedVerifyLoadedWire67.advance_eq_recover
            hash message pk wire initial entry loaded frame g small leaf0
            (GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 g)
      simpa only [GroupedBalancedVerifyGroupFold67.callsAt,
        GroupedBalancedVerifyLoadedWire67.base_step45 g small,
        GroupedBalancedVerifyLoadedWire67.leaf_step45 leaf0 g small,
        GroupedBalancedVerifyLoadedWire67.offset_step45 g small,
        nextRoot,Nat.add_assoc] using prev

theorem callsAt45_eq_layersCalls (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (leaf0 : Nat) :
    GroupedBalancedVerifyGroupFold67.callsAt hash entry leaf0 45 =
      layersCalls hash GroupedBalancedScheme67.Heights 10 leaf0
        (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry)
        (GroupedBalancedWireUpper67.upperList wire
          GroupedBalancedScheme67.Heights 208) := by
  have counted := calls_prefix hash message pk wire initial entry loaded frame
    leaf0 45 (by decide)
  have done : GroupedBalancedScheme67.Heights.drop 45 = [] := by
    apply List.drop_eq_nil_of_le
    rw [GroupedBalancedScheme67.heights_length]
  rw [done] at counted
  simp only [wireLayersCalls,add_zero] at counted
  rw [layersCalls_wire]
  exact counted.symm

#print axioms calls_recoverBottom
#print axioms calls_recoverLeaf
#print axioms calls_recoverUpper
#print axioms calls_recoverLayers
#print axioms calls_verify
#print axioms callsAt45_eq_layersCalls
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyCallBridge67
