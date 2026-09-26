import SigGolfCandidate.Hypertree.GroupedBalancedVerifyReferenceBridge67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWireDigest67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyGroupFold67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyUpperBridge67

/-! Aligned slices of the supplied wire are the loaded verifier digest words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem initial_digest (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some s)
    (offset : Nat) (bound : offset+16 ≤ 50848)
    (aligned : offset % 8 = 0) :
    s.getMem (BitVec.ofNat 64 (0x2c700+offset+8)) ++
      s.getMem (BitVec.ofNat 64 (0x2c700+offset)) =
        SignatureEncoding.slice wire offset 16 := by
  refine GroupedBalancedVerifyWireDigest67.pair_eq_slice s wire
    (0x2c700+offset) offset (by omega) (by omega) bound ?_
  intro j hj
  simpa only [Nat.add_assoc] using
    GroupedBalancedVerifyReferenceBridge67.initial_wire_byte
      message pk wire s loaded (offset+j) (by omega)

theorem initial_pk_digest (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some s) :
    s.getMem 0x48 ++ s.getMem 0x40 = pk := by
  have fromWords := GroupedBalancedVerifyWireDigest67.pair_read
    s 0x40 (by decide) (by decide)
  have fromBytes : readBuffer s 0x40 16 = pk := by
    apply SigGolfCandidate.Memory.readBuffer_of_bytes
    intro j hj
    simpa only [bytes,List.getElem_map,List.getElem_range] using
      GroupedBalancedVerifyReferenceBridge67.initial_pk_byte
        message pk wire s loaded j hj
  simpa only [show BitVec.ofNat 64 (0x40+8) = (0x48 : Word) by decide,
    show BitVec.ofNat 64 0x40 = (0x40 : Word) by decide] using
    fromWords.symm.trans fromBytes

def offsetAt (g : Nat) : Nat :=
  208+16*67*g+16*GroupedBalancedVerifyGroupFold67.accumulatedHeight g

theorem startAt_eq (g : Nat) :
    GroupedBalancedVerifyGroupFold67.startAt g = 0x2c700+offsetAt g := by
  unfold GroupedBalancedVerifyGroupFold67.startAt offsetAt
  omega

theorem initial_witness_digest (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some s)
    (g : Nat) (hg : g < 45) (chain : Fin 67) :
    GroupedBalancedVerifyGenericPath67.witnessDigest s
      (GroupedBalancedVerifyGroupFold67.startAt g) chain =
      SignatureEncoding.slice wire (offsetAt g+16*chain.val) 16 := by
  have whole := GroupedBalancedVerifyGroupFold67.wire_bound g hg
  have h := initial_digest message pk wire s loaded
    (offsetAt g+16*chain.val) (by
      rw [startAt_eq] at whole
      have hc := chain.isLt
      unfold offsetAt at *
      omega) (by unfold offsetAt; omega)
  simpa only [GroupedBalancedVerifyGenericPath67.witnessDigest,
    startAt_eq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem initial_sibling_digest (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some s)
    (g j : Nat) (hg : g < 45)
    (hj : j < GroupedBalancedVerifyGroupFold67.heightAt g) :
    GroupedBalancedVerifyGenericPath67.siblingDigest s
      (GroupedBalancedVerifyGroupFold67.startAt g) j =
      SignatureEncoding.slice wire (offsetAt g+16*(67+j)) 16 := by
  have whole := GroupedBalancedVerifyGroupFold67.wire_bound g hg
  have h := initial_digest message pk wire s loaded
    (offsetAt g+16*(67+j)) (by
      rw [startAt_eq] at whole
      unfold offsetAt at *
      omega) (by unfold offsetAt; omega)
  simpa only [GroupedBalancedVerifyGenericPath67.siblingDigest,
    startAt_eq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
    Nat.mul_add] using h

theorem advance_eq_recover (hash : Hash)
    (message : Message) (pk : PublicKey) (wire : Bytes 50848)
    (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (g : Nat) (hg : g < 45) (leaf0 : Nat)
    (root : Reference.Digest) :
    GroupedBalancedVerifyGroupFold67.advanceRoot hash entry
      (GroupedBalancedVerifyGroupFold67.baseAt g)
      (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g)
      (GroupedBalancedVerifyGroupFold67.startAt g)
      (GroupedBalancedVerifyGroupFold67.heightAt g) root =
    GroupedBalancedUpperTree67.recover hash
      (GroupedBalancedVerifyGroupFold67.baseAt g)
      (GroupedBalancedVerifyGroupFold67.heightAt g)
      (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g /
        2^GroupedBalancedVerifyGroupFold67.heightAt g)
      (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g)
      root
      (GroupedBalancedWireWitness67.upperWitness wire
        (GroupedBalancedVerifyGroupFold67.heightAt g) (offsetAt g)) := by
  let base := GroupedBalancedVerifyGroupFold67.baseAt g
  let leaf := GroupedBalancedVerifyGroupFold67.leafAt leaf0 g
  let start := GroupedBalancedVerifyGroupFold67.startAt g
  let height := GroupedBalancedVerifyGroupFold67.heightAt g
  let witness := GroupedBalancedWireWitness67.upperWitness wire height (offsetAt g)
  have valuesEq :
      GroupedBalancedVerifyGenericPath67.witnessDigest entry start =
        GroupedBalancedVerifyUpperBridge67.leafValues witness := by
    funext chain
    rw [GroupedBalancedVerifyWireFrame67.witness_digest_frame initial entry
      start height (GroupedBalancedVerifyGroupFold67.wire_bound g hg)
      frame chain]
    simpa only [base,leaf,start,height,witness,
      GroupedBalancedVerifyUpperBridge67.leafValues_upper] using
      initial_witness_digest message pk wire initial loaded g hg chain
  have siblingsEq : ∀ j, j < height →
      GroupedBalancedVerifyGenericPath67.siblingDigest entry start j =
        GroupedBalancedVerifyUpperBridge67.siblingAt witness j := by
    intro j hj
    rw [GroupedBalancedVerifyWireFrame67.sibling_digest_frame initial entry
      start height j (GroupedBalancedVerifyGroupFold67.wire_bound g hg)
      hj frame]
    rw [show start = GroupedBalancedVerifyGroupFold67.startAt g from rfl]
    rw [initial_sibling_digest message pk wire initial loaded g j hg hj]
    simpa only [height,witness,
      GroupedBalancedVerifyUpperBridge67.siblingAt_upper wire
        (GroupedBalancedVerifyGroupFold67.heightAt g) (offsetAt g) j hj]
  have siblingsRoot :=
    GroupedBalancedVerifyWireFrame67.rootAt_siblings_congr hash
      base leaf
      (GroupedBalancedUpperTree67.compressLeaf hash base leaf
        (GroupedBalancedByteFastEndpointAccum67.expectedEndpoint hash
          base leaf root
          (GroupedBalancedVerifyUpperBridge67.leafValues witness)))
      (GroupedBalancedVerifyGenericPath67.siblingDigest entry start)
      (GroupedBalancedVerifyUpperBridge67.siblingAt witness) height siblingsEq
  have recover := GroupedBalancedVerifyUpperBridge67.recover_eq_rootAt
    hash base leaf root witness
  simpa only [GroupedBalancedVerifyGroupFold67.advanceRoot,
    base,leaf,start,height,witness,valuesEq] using siblingsRoot.trans recover.symm

def wireRecoverLayers (hash : Hash) (wire : Bytes 50848) :
    (heights : List Nat) → (base index start : Nat) →
      Reference.Digest → Reference.Digest
  | [], _, _, _, root => root
  | height :: rest, base, index, start, root =>
      let tree := index/2^height
      wireRecoverLayers hash wire rest (base+height) tree
        (start+16*(67+height))
        (GroupedBalancedUpperTree67.recover hash base height tree index root
          (GroupedBalancedWireWitness67.upperWitness wire height start))

theorem recoverLayers_wire (hash : Hash) (wire : Bytes 50848)
    (heights : List Nat) (base index start : Nat)
    (root : Reference.Digest) :
    GroupedBalancedScheme67.recoverLayers hash heights base index root
      (GroupedBalancedWireUpper67.upperList wire heights start) =
    wireRecoverLayers hash wire heights base index start root := by
  induction heights generalizing base index start root with
  | nil => rfl
  | cons height rest ih =>
    simp only [GroupedBalancedScheme67.recoverLayers,
      GroupedBalancedWireUpper67.upperList,wireRecoverLayers]
    exact ih _ _ _ _

theorem height_get (g : Nat) (hg : g < 45) :
    GroupedBalancedScheme67.Heights[g]'(by
      rw [GroupedBalancedScheme67.heights_length]
      exact hg) = GroupedBalancedVerifyGroupFold67.heightAt g := by
  simp only [GroupedBalancedScheme67.Heights,
    GroupedBalancedVerifyGroupFold67.heightAt]
  by_cases small : g < 30
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_replicate,if_pos small]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_replicate,if_neg small]

theorem heights_drop_step (g : Nat) (hg : g < 45) :
    GroupedBalancedScheme67.Heights.drop g =
      GroupedBalancedVerifyGroupFold67.heightAt g ::
        GroupedBalancedScheme67.Heights.drop (g+1) := by
  rw [List.drop_eq_getElem_cons (by
    rw [GroupedBalancedScheme67.heights_length]
    exact hg)]
  rw [height_get g hg]

theorem accumulated_step45 (g : Nat) (hg : g < 45) :
    GroupedBalancedVerifyGroupFold67.accumulatedHeight (g+1) =
      GroupedBalancedVerifyGroupFold67.accumulatedHeight g+
        GroupedBalancedVerifyGroupFold67.heightAt g := by
  unfold GroupedBalancedVerifyGroupFold67.accumulatedHeight
    GroupedBalancedVerifyGroupFold67.heightAt
  split_ifs <;> omega

theorem base_step45 (g : Nat) (hg : g < 45) :
    GroupedBalancedVerifyGroupFold67.baseAt (g+1) =
      GroupedBalancedVerifyGroupFold67.baseAt g+
        GroupedBalancedVerifyGroupFold67.heightAt g := by
  simp only [GroupedBalancedVerifyGroupFold67.baseAt,accumulated_step45 g hg]
  omega

theorem offset_step45 (g : Nat) (hg : g < 45) :
    offsetAt (g+1) = offsetAt g+
      16*(67+GroupedBalancedVerifyGroupFold67.heightAt g) := by
  simp only [offsetAt,accumulated_step45 g hg]
  omega

theorem leaf_step45 (leaf0 g : Nat) (hg : g < 45) :
    GroupedBalancedVerifyGroupFold67.leafAt leaf0 (g+1) =
      GroupedBalancedVerifyGroupFold67.leafAt leaf0 g /
        2^GroupedBalancedVerifyGroupFold67.heightAt g := by
  simp only [GroupedBalancedVerifyGroupFold67.leafAt,
    accumulated_step45 g hg,pow_add]
  rw [Nat.div_div_eq_div_mul]

theorem upper_root_fold (hash : Hash) (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (leaf0 g : Nat) (hg : g ≤ 45) :
    wireRecoverLayers hash wire GroupedBalancedScheme67.Heights 10
      leaf0 208 (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry) =
    wireRecoverLayers hash wire (GroupedBalancedScheme67.Heights.drop g)
      (GroupedBalancedVerifyGroupFold67.baseAt g)
      (GroupedBalancedVerifyGroupFold67.leafAt leaf0 g)
      (offsetAt g)
      (GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 g) := by
  induction g with
  | zero =>
      simp only [List.drop_zero,
        GroupedBalancedVerifyGroupFold67.base_zero,
        GroupedBalancedVerifyGroupFold67.leaf_zero,
        GroupedBalancedVerifyGroupFold67.rootAt,
        offsetAt,GroupedBalancedVerifyGroupFold67.accumulated_zero,
        Nat.mul_zero,Nat.add_zero]
  | succ g ih =>
      have small : g < 45 := by omega
      have prev := ih (by omega)
      rw [heights_drop_step g small] at prev
      simp only [wireRecoverLayers] at prev
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
              (GroupedBalancedVerifyGroupFold67.heightAt g) (offsetAt g)) := by
        simpa only [GroupedBalancedVerifyGroupFold67.rootAt] using
          advance_eq_recover hash message pk wire initial entry loaded frame
            g small leaf0
            (GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 g)
      simpa only [base_step45 g small,leaf_step45 leaf0 g small,
        offset_step45 g small,nextRoot] using prev

theorem root45_eq_recoverLayers (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (leaf0 : Nat) :
    GroupedBalancedVerifyGroupFold67.rootAt hash entry leaf0 45 =
      GroupedBalancedScheme67.recoverLayers hash GroupedBalancedScheme67.Heights
        10 leaf0 (GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry)
        (GroupedBalancedWireUpper67.upperList wire
          GroupedBalancedScheme67.Heights 208) := by
  have fold := upper_root_fold hash message pk wire initial entry loaded frame
    leaf0 45 (by decide)
  have done : GroupedBalancedScheme67.Heights.drop 45 = [] := by
    apply List.drop_eq_nil_of_le
    rw [GroupedBalancedScheme67.heights_length]
  rw [done] at fold
  simp only [wireRecoverLayers] at fold
  rw [recoverLayers_wire] 
  exact fold.symm

#print axioms initial_digest
#print axioms initial_pk_digest
#print axioms initial_witness_digest
#print axioms initial_sibling_digest
#print axioms advance_eq_recover
#print axioms recoverLayers_wire
#print axioms heights_drop_step
#print axioms root45_eq_recoverLayers
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
