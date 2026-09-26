import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideWords67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeAdvance67

/-! Composition of a child arrangement and its node hash/edge advance. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def OutsideChildren (a : Word) : Prop :=
  ∀ i : Fin 4, a ≠ Signing.wordAddress 0x80520 i.val

theorem arranged_advance (hash : Hash) (s arranged : MachineState)
    (sideSteps sideCycles level tree : Nat)
    (left right : Reference.Digest)
    (path : Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
      sideSteps sideCycles 0 0 arranged)
    (pc : arranged.pc = 0x1880)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (children : ∀ i : Fin 4,
      arranged.getMem (Signing.wordAddress 0x80520 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64)
    (frame : ∀ a : Word, OutsideChildren a →
      arranged.getMem a = s.getMem a) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        (sideSteps+105) (sideCycles+112) 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree left right).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          s.getMem (Signing.wordAddress 0x81008 i.val)) := by
  have carried (a : Word) (high : 0x81000 ≤ a.toNat) :
      arranged.getMem a = s.getMem a := by
    apply frame a
    intro i
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80520+8*i.val < 2^64)] at h
    omega
  have arrangedLevel : arranged.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [carried 0x81000 (by decide)]
    exact hlevel
  have arrangedIndex : ∀ i : Fin 3,
      arranged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [carried _ (by fin_cases i <;> decide)]
    exact hindex i
  obtain ⟨final,nodeTrace,done,root,ptr,count,levelCount,index⟩ :=
    GroupedBalancedByteFastNodeAdvance67.node_advance hash arranged
      level tree left right pc arrangedLevel arrangedIndex children
  refine ⟨final,?_,done,root,?_,?_,?_,?_⟩
  · exact path.trans nodeTrace
  · rw [ptr,carried 0x81048 (by decide)]
  · rw [count,carried 0x81000 (by decide)]
  · rw [levelCount,carried 0x81050 (by decide)]
  · intro i
    rw [index i,carried _ (by fin_cases i <;> decide)]

theorem right_advance (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x17dc)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        right.extractLsb' (64*half.val) 64)
    (sibling : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        left.extractLsb' (64*half.val) 64)
    (separate : ∀ half : Fin 2, ∀ i, i < 2 →
      s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80530 i) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        132 139 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree left right).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          s.getMem (Signing.wordAddress 0x81008 i.val)) := by
  obtain ⟨arranged,path,arrangedPC,children,frame⟩ :=
    GroupedBalancedByteFastSideWords67.right_side_words hash s
      left right pc ptr0 ptr8 root sibling separate
  have result := arranged_advance hash s arranged 27 27 level tree
    left right (by simpa [GroupedBalancedByteFastSideWords67.image] using path)
    arrangedPC hlevel hindex children (by exact frame)
  simpa using result

theorem left_advance (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x1830)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (root : ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        left.extractLsb' (64*half.val) 64)
    (sibling : ∀ half : Fin 2,
      s.getMem (s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val)) =
        right.extractLsb' (64*half.val) 64)
    (separate : ∀ half : Fin 2, ∀ i, i < 2 →
      s.getMem 0x81048 + BitVec.ofNat 64 (8*half.val) ≠
        Signing.wordAddress 0x80520 i) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        131 138 1 1 final ∧
      (final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree left right).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x81048 = s.getMem 0x81048 + 16 ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      final.getMem 0x81050 = s.getMem 0x81050 + 1 ∧
      (∀ i : Fin 3,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          s.getMem (Signing.wordAddress 0x81008 i.val)) := by
  obtain ⟨arranged,path,arrangedPC,children,frame⟩ :=
    GroupedBalancedByteFastSideWords67.left_side_words hash s
      left right pc ptr0 ptr8 root sibling separate
  have result := arranged_advance hash s arranged 26 26 level tree
    left right (by simpa [GroupedBalancedByteFastSideWords67.image] using path)
    arrangedPC hlevel hindex children (by exact frame)
  simpa using result

#print axioms arranged_advance
#print axioms right_advance
#print axioms left_advance

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideAdvance67
