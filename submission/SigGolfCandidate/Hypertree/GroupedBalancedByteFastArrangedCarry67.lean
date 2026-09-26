import SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeAdvance67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastSideAdvance67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCounter67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastArrangedCarry67. -/
section
/-! Counter and witness-frame facts for any certified node/advance trace. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCounter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem low_ne (a : Word) (low : a.toNat < 0x80000)
    (base : Nat) (high : 0x80000 ≤ base)
    (small : base+8*4 < 2^64) (i : Fin 4) :
    a ≠ Signing.wordAddress base i.val := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : base+8*i.val < 2^64)] at h
  omega

theorem counter_of_trace (hash : Hash) (s final : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x1880)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hchildren : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80520 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64)
    (trace : Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
      105 112 1 1 final) :
    (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
      then 0x1758 else 0x19c4) ∧
    final.getMem 0x81060 = s.getMem 0x81060 ∧
    final.getMem 0x81058 = s.getMem 0x81058 ∧
    (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
    (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  obtain ⟨node,first,nodePC,_,nodeFrame⟩ :=
    GroupedBalancedByteFastNodeCoreWords67.node_core_words hash s
      level tree left right pc hlevel hindex hchildren
  let concrete := GroupedBalancedByteFastEdgeUpdate67.updateState node
  have second := GroupedBalancedByteFastEdgeUpdate67.update_block node nodePC
  have concreteTrace : Trace hash GroupedBalancedVerifyImage67Fast2Byte.image
      s 105 112 1 1 concrete := by
    have path := first.trans (OrdinarySteps.trace (hash := hash) second)
    simpa [concrete,GroupedBalancedByteFastNodeCoreWords67.image,
      GroupedBalancedByteFastEdgeUpdate67.image] using path
  have eq := Trace.deterministic trace concreteTrace
  subst final
  have node50 : node.getMem 0x81050 = s.getMem 0x81050 :=
    nodeFrame 0x81050 (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  have node60 : node.getMem 0x81060 = s.getMem 0x81060 :=
    nodeFrame 0x81060 (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  have node58 : node.getMem 0x81058 = s.getMem 0x81058 :=
    nodeFrame 0x81058 (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
      (by intro i; fin_cases i <;> decide)
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := GroupedBalancedByteFastEdgeUpdate67.update_pc node nodePC
    rw [update_reg_count,update_reg_limit,node50,node60] at h
    exact h
  · rw [update_mem node 0x81060 (by decide) (by decide) (by decide)]
    exact node60
  · rw [update_mem node 0x81058 (by decide) (by decide) (by decide)]
    exact node58
  · intro a low
    have nodeLow : node.getMem a = s.getMem a :=
      nodeFrame a
        (fun i => low_ne a low 0x80020 (by decide) (by decide) i)
        (fun i => low_ne a low 0x80000 (by decide) (by decide) i)
        (fun i => low_ne a low 0x80300 (by decide) (by decide) i)
        (fun i => low_ne a low 0x80500 (by decide) (by decide)
          ⟨i.val,by omega⟩)
    have neq (n : Nat) (big : 0x80000 ≤ n) (small : n < 2^64) :
        a ≠ BitVec.ofNat 64 n := by
      intro same
      have h := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h
      omega
    rw [update_mem node a
      (neq 0x81048 (by decide) (by decide))
      (neq 0x81000 (by decide) (by decide))
      (neq 0x81050 (by decide) (by decide))]
    exact nodeLow
  · intro a high
    have neq (b : Nat) (small : b < 0xfff700) :
        a ≠ BitVec.ofNat 64 b := by
      intro same
      have h := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : b < 2^64)] at h
      omega
    have outside (base n : Nat)
        (small : base+8*n < 0xfff700) :
        ∀ i : Fin n, a ≠ Signing.wordAddress base i.val := by
      intro i same
      have h := congrArg BitVec.toNat same
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : base+8*i.val < 2^64)] at h
      omega
    have nodeHigh : node.getMem a = s.getMem a :=
      nodeFrame a
        (outside 0x80020 4 (by decide))
        (outside 0x80000 4 (by decide))
        (outside 0x80300 4 (by decide))
        (outside 0x80500 2 (by decide))
    rw [update_mem node a
      (neq 0x81048 (by decide))
      (neq 0x81000 (by decide))
      (neq 0x81050 (by decide))]
    exact nodeHigh

#print axioms counter_of_trace

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCounter67

end

/-! Loop counter, group control, and witness carry across an arranged node. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastArrangedCarry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem outside_low (a : Word) (low : a.toNat < 0x80000) :
    GroupedBalancedByteFastSideAdvance67.OutsideChildren a := by
  intro i eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80520 + 8*i.val < 2^64)] at h
  omega

private theorem outside_high (a : Word) (high : 0x81000 ≤ a.toNat) :
    GroupedBalancedByteFastSideAdvance67.OutsideChildren a := by
  intro i eq
  have h := congrArg BitVec.toNat eq
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80520 + 8*i.val < 2^64)] at h
  omega

theorem arranged_carry (hash : Hash) (s arranged : MachineState)
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
    (frame : ∀ a : Word,
      GroupedBalancedByteFastSideAdvance67.OutsideChildren a →
        arranged.getMem a = s.getMem a) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image s
        (sideSteps+105) (sideCycles+112) 1 1 final ∧
      (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
        then 0x1758 else 0x19c4) ∧
      final.getMem 0x81060 = s.getMem 0x81060 ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  have carried (a : Word) (high : 0x81000 ≤ a.toNat) :
      arranged.getMem a = s.getMem a :=
    frame a (outside_high a high)
  have arrangedLevel : arranged.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [carried 0x81000 (by decide)]
    exact hlevel
  have arrangedIndex : ∀ i : Fin 3,
      arranged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [carried _ (by fin_cases i <;> decide)]
    exact hindex i
  obtain ⟨final,nodeTrace,_,_,_,_,_,_⟩ :=
    GroupedBalancedByteFastNodeAdvance67.node_advance hash arranged
      level tree left right pc arrangedLevel arrangedIndex children
  obtain ⟨finalPC,limit,group,low,tableFrame⟩ :=
    GroupedBalancedByteFastNodeCounter67.counter_of_trace hash arranged final
      level tree left right pc arrangedLevel arrangedIndex children nodeTrace
  refine ⟨final,path.trans nodeTrace,?_,?_,?_,?_,?_⟩
  · rw [finalPC,carried 0x81050 (by decide),carried 0x81060 (by decide)]
  · rw [limit,carried 0x81060 (by decide)]
  · rw [group,carried 0x81058 (by decide)]
  · intro a aLow
    rw [low a aLow]
    exact frame a (outside_low a aLow)
  · intro a high
    rw [tableFrame a high]
    exact frame a (outside_high a (by omega))

theorem right_side_carry (hash : Hash) (s : MachineState)
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
      (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
        then 0x1758 else 0x19c4) ∧
      final.getMem 0x81060 = s.getMem 0x81060 ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  obtain ⟨arranged,path,arrangedPC,children,frame⟩ :=
    GroupedBalancedByteFastSideWords67.right_side_words hash s
      left right pc ptr0 ptr8 root sibling separate
  have result := arranged_carry hash s arranged 27 27 level tree left right
    (by simpa [GroupedBalancedByteFastSideWords67.image] using path)
    arrangedPC hlevel hindex children (by exact frame)
  simpa using result

theorem left_side_carry (hash : Hash) (s : MachineState)
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
      (final.pc = if s.getMem 0x81050 + 1 ≠ s.getMem 0x81060
        then 0x1758 else 0x19c4) ∧
      final.getMem 0x81060 = s.getMem 0x81060 ∧
      final.getMem 0x81058 = s.getMem 0x81058 ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a = s.getMem a) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat → final.getMem a = s.getMem a) := by
  obtain ⟨arranged,path,arrangedPC,children,frame⟩ :=
    GroupedBalancedByteFastSideWords67.left_side_words hash s
      left right pc ptr0 ptr8 root sibling separate
  have result := arranged_carry hash s arranged 26 26 level tree left right
    (by simpa [GroupedBalancedByteFastSideWords67.image] using path)
    arrangedPC hlevel hindex children (by exact frame)
  simpa using result

#print axioms arranged_carry
#print axioms right_side_carry
#print axioms left_side_carry

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastArrangedCarry67
