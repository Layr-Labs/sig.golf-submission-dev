import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeControlFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalData67

/-! Functional authentication siblings at all levels of an upper Merkle call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingAllData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
open GroupedBalancedSignUpperTreeFirstLevelData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt
private abbrev sib := GroupedBalancedSignUpperSelectedSiblingIndex67.siblingIndex

private theorem slot_before (witnessBase level earlier : Nat) (i : Fin 2)
    (early : earlier<level)
    (bound : witnessBase+16*level+16≤0x80000) :
    (BitVec.ofNat 64 (witnessBase+16*earlier+8*i.val)).toNat<
      witnessBase+16*level := by
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega :
    witnessBase+16*earlier+8*i.val<2^64)]
  omega

theorem height3 (hash : Hash) (treeBase leafBase witnessBase addressBase
    selected : Nat) (leaves : Nat → Reference.Digest)
    (s final : MachineState)
    (params : Params leafBase 0 4 0x83000 0x88000 addressBase)
    (start : Start hash treeBase leafBase leaves 3 witnessBase 0 4
      0x83000 0x88000 addressBase s)
    (selectedWord : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (selectedBound : selected<2^3)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 882 931 7 7 final) :
    ∀ level, level<3 → ∀ i : Fin 2,
      final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        (node hash treeBase leafBase leaves level
          (Nat.xor (selected/2^level) 1)).extractLsb' (64*i.val) 64 := by
  obtain ⟨s1,t0,p1,start1⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 3 witnessBase 0 4 0x83000 0x88000 addressBase s
      params start (by decide) (Or.inl rfl) treeBound witnessBound
      witnessAligned (by decide) (by decide) (Or.inr (Or.inl rfl))
  obtain ⟨s2,t1,p2,start2⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 3 witnessBase 1 2 0x88000 0x83000 (addressBase/2)
      s1 (by simpa only [show 4/2=2 by decide] using p1)
      (by simpa only [show 4/2=2 by decide] using start1)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inl rfl)
  obtain ⟨built,t2,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalData67.terminal_root hash treeBase
      leafBase leaves 3 witnessBase 2 0x83000 0x88000
      ((addressBase/2)/2) s2
      (by simpa only [show 2/2=1 by decide] using p2)
      (by simpa only [show 2/2=1 by decide] using start2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
  have builtTrace : Trace hash image s 882 931 7 7 built := by
    have combined := (t0.trans t1).trans t2
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  have chosen1 : s1.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.height_step_frame hash s s1
      3 treeBase witnessBase 0 4 0x83000 0x88000 start.ready (by decide)
      (Or.inl rfl) witnessBound witnessAligned (by decide) (by decide)
      (Or.inl ⟨rfl,rfl⟩) t0 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      selectedWord
  have chosen2 : s2.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.height_step_frame hash s1 s2
      3 treeBase witnessBase 1 2 0x88000 0x83000 start1.ready
      (by decide) (Or.inl rfl) witnessBound witnessAligned (by decide)
      (by decide) (Or.inr ⟨rfl,rfl⟩) t1 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      chosen1
  have idx0 : sib s<8 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s 3 0
        selected (by decide) (by decide) selectedWord
        start.ready.levelWord selectedBound
  have idx1 : sib s1<4 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s1 3 1
        selected (by decide) (by decide) chosen1
        start1.ready.levelWord selectedBound
  have idx2 : sib s2<2 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s2 3 2
        selected (by decide) (by decide) chosen2
        start2.ready.levelWord selectedBound
  have input0 : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*sib s+8*i.val))=
        (node hash treeBase leafBase leaves 0 (sib s)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start.sourceWords (sib s) (by simpa using idx0) i
  have input1 : ∀ i : Fin 2,
      s1.getMem (BitVec.ofNat 64 (0x88000+16*sib s1+8*i.val))=
        (node hash treeBase leafBase leaves 1 (sib s1)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start1.sourceWords (sib s1) (by simpa using idx1) i
  have input2 : ∀ i : Fin 2,
      s2.getMem (BitVec.ofNat 64 (0x83000+16*sib s2+8*i.val))=
        (node hash treeBase leafBase leaves 2 (sib s2)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start2.sourceWords (sib s2) (by simpa using idx2) i
  have sib0 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.height_step_sibling
      hash s s1 3 treeBase witnessBase 0 4 0x83000 0x88000
      (node hash treeBase leafBase leaves 0 (sib s)) start.ready
      (by decide) (Or.inl rfl) witnessBound witnessAligned
      (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) input0 t0
  have sib1 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.height_step_sibling
      hash s1 s2 3 treeBase witnessBase 1 2 0x88000 0x83000
      (node hash treeBase leafBase leaves 1 (sib s1)) start1.ready
      (by decide) (Or.inl rfl) witnessBound witnessAligned
      (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) input1 t1
  have sib2 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.terminal_sibling
      hash s2 built 3 treeBase witnessBase 2 0x83000 0x88000
      (node hash treeBase leafBase leaves 2 (sib s2)) start2.ready
      (by decide) (Or.inl rfl) witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩) input2 t2
  have eq0 : sib s=Nat.xor (selected/2^0) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s 0 selected
      (by decide) (by omega) selectedWord start.ready.levelWord
  have eq1 : sib s1=Nat.xor (selected/2^1) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s1 1 selected
      (by decide) (by omega) chosen1 start1.ready.levelWord
  have eq2 : sib s2=Nat.xor (selected/2^2) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s2 2 selected
      (by decide) (by omega) chosen2 start2.ready.levelWord
  intro level levelBound i
  have cases : level=0 ∨ level=1 ∨ level=2 := by omega
  rcases cases with rfl|rfl|rfl
  · have prior1 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.height_step_prior
        hash s1 s2 3 treeBase witnessBase 1 2 0x88000 0x83000
        start1.ready (by decide) (Or.inl rfl) witnessBound
        witnessAligned (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
        t1 (BitVec.ofNat 64 (witnessBase+16*0+8*i.val))
        (slot_before witnessBase 1 0 i (by decide) (by omega))
    have prior2 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.terminal_prior
        hash s2 built 3 treeBase witnessBase 2 0x83000 0x88000
        start2.ready (by decide) (Or.inl rfl) witnessBound
        witnessAligned (Or.inl ⟨rfl,rfl⟩) t2
        (BitVec.ofNat 64 (witnessBase+16*0+8*i.val))
        (slot_before witnessBase 2 0 i (by decide) (by omega))
    rw [same,prior2,prior1]
    rw [eq0] at sib0
    simpa only [Nat.mul_zero,Nat.zero_add] using sib0 i
  · have prior :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.terminal_prior
        hash s2 built 3 treeBase witnessBase 2 0x83000 0x88000
        start2.ready (by decide) (Or.inl rfl) witnessBound
        witnessAligned (Or.inl ⟨rfl,rfl⟩) t2
        (BitVec.ofNat 64 (witnessBase+16*1+8*i.val))
        (slot_before witnessBase 2 1 i (by decide) (by omega))
    rw [same,prior]
    rw [eq1] at sib1
    simpa only [Nat.mul_one] using sib1 i
  · rw [same]
    rw [eq2] at sib2
    simpa only [Nat.reduceMul] using sib2 i

theorem height4 (hash : Hash) (treeBase leafBase witnessBase addressBase
    selected : Nat) (leaves : Nat → Reference.Digest)
    (s final : MachineState)
    (params : Params leafBase 0 8 0x83000 0x88000 addressBase)
    (start : Start hash treeBase leafBase leaves 4 witnessBase 0 8
      0x83000 0x88000 addressBase s)
    (selectedWord : s.getMem 0x810e8=BitVec.ofNat 64 selected)
    (selectedBound : selected<2^4)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (trace : Trace hash image s 1668 1773 15 15 final) :
    ∀ level, level<4 → ∀ i : Fin 2,
      final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        (node hash treeBase leafBase leaves level
          (Nat.xor (selected/2^level) 1)).extractLsb' (64*i.val) 64 := by
  obtain ⟨s1,t0,p1,start1⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 0 8 0x83000 0x88000 addressBase s
      params start (by decide) (Or.inr rfl) treeBound witnessBound
      witnessAligned (by decide) (by decide) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨s2,t1,p2,start2⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 1 4 0x88000 0x83000 (addressBase/2)
      s1 (by simpa only [show 8/2=4 by decide] using p1)
      (by simpa only [show 8/2=4 by decide] using start1)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inr (Or.inl rfl))
  obtain ⟨s3,t2,p3,start3⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 2 2 0x83000 0x88000
      ((addressBase/2)/2) s2
      (by simpa only [show 4/2=2 by decide] using p2)
      (by simpa only [show 4/2=2 by decide] using start2)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inl rfl)
  obtain ⟨built,t3,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalData67.terminal_root hash treeBase
      leafBase leaves 4 witnessBase 3 0x88000 0x83000
      (((addressBase/2)/2)/2) s3
      (by simpa only [show 2/2=1 by decide] using p3)
      (by simpa only [show 2/2=1 by decide] using start3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
  have builtTrace : Trace hash image s 1668 1773 15 15 built := by
    have combined := ((t0.trans t1).trans t2).trans t3
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  have chosen1 : s1.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.height_step_frame hash s s1
      4 treeBase witnessBase 0 8 0x83000 0x88000 start.ready (by decide)
      (Or.inr rfl) witnessBound witnessAligned (by decide) (by decide)
      (Or.inl ⟨rfl,rfl⟩) t0 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      selectedWord
  have chosen2 : s2.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.height_step_frame hash s1 s2
      4 treeBase witnessBase 1 4 0x88000 0x83000 start1.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned (by decide)
      (by decide) (Or.inr ⟨rfl,rfl⟩) t1 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      chosen1
  have chosen3 : s3.getMem 0x810e8=BitVec.ofNat 64 selected :=
    (GroupedBalancedSignUpperTreeControlFrame67.height_step_frame hash s2 s3
      4 treeBase witnessBase 2 2 0x83000 0x88000 start2.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned (by decide)
      (by decide) (Or.inl ⟨rfl,rfl⟩) t2 0x810e8
      (by simp [GroupedBalancedSignUpperTreeControlFrame67.Safe])).trans
      chosen2
  have idx0 : sib s<16 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s 4 0
        selected (by decide) (by decide) selectedWord
        start.ready.levelWord selectedBound
  have idx1 : sib s1<8 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s1 4 1
        selected (by decide) (by decide) chosen1
        start1.ready.levelWord selectedBound
  have idx2 : sib s2<4 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s2 4 2
        selected (by decide) (by decide) chosen2
        start2.ready.levelWord selectedBound
  have idx3 : sib s3<2 := by
    simpa [sib] using
      GroupedBalancedSignUpperSelectedSiblingIndex67.index_bound s3 4 3
        selected (by decide) (by decide) chosen3
        start3.ready.levelWord selectedBound
  have input0 : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*sib s+8*i.val))=
        (node hash treeBase leafBase leaves 0 (sib s)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start.sourceWords (sib s) (by simpa using idx0) i
  have input1 : ∀ i : Fin 2,
      s1.getMem (BitVec.ofNat 64 (0x88000+16*sib s1+8*i.val))=
        (node hash treeBase leafBase leaves 1 (sib s1)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start1.sourceWords (sib s1) (by simpa using idx1) i
  have input2 : ∀ i : Fin 2,
      s2.getMem (BitVec.ofNat 64 (0x83000+16*sib s2+8*i.val))=
        (node hash treeBase leafBase leaves 2 (sib s2)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start2.sourceWords (sib s2) (by simpa using idx2) i
  have input3 : ∀ i : Fin 2,
      s3.getMem (BitVec.ofNat 64 (0x88000+16*sib s3+8*i.val))=
        (node hash treeBase leafBase leaves 3 (sib s3)).extractLsb'
          (64*i.val) 64 := by
    intro i
    exact start3.sourceWords (sib s3) (by simpa using idx3) i
  have sib0 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.height_step_sibling
      hash s s1 4 treeBase witnessBase 0 8 0x83000 0x88000
      (node hash treeBase leafBase leaves 0 (sib s)) start.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned
      (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) input0 t0
  have sib1 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.height_step_sibling
      hash s1 s2 4 treeBase witnessBase 1 4 0x88000 0x83000
      (node hash treeBase leafBase leaves 1 (sib s1)) start1.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned
      (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩) input1 t1
  have sib2 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.height_step_sibling
      hash s2 s3 4 treeBase witnessBase 2 2 0x83000 0x88000
      (node hash treeBase leafBase leaves 2 (sib s2)) start2.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned
      (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩) input2 t2
  have sib3 :=
    GroupedBalancedSignUpperSelectedTreeSiblingStepData67.terminal_sibling
      hash s3 built 4 treeBase witnessBase 3 0x88000 0x83000
      (node hash treeBase leafBase leaves 3 (sib s3)) start3.ready
      (by decide) (Or.inr rfl) witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩) input3 t3
  have eq0 : sib s=Nat.xor (selected/2^0) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s 0 selected
      (by decide) (by omega) selectedWord start.ready.levelWord
  have eq1 : sib s1=Nat.xor (selected/2^1) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s1 1 selected
      (by decide) (by omega) chosen1 start1.ready.levelWord
  have eq2 : sib s2=Nat.xor (selected/2^2) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s2 2 selected
      (by decide) (by omega) chosen2 start2.ready.levelWord
  have eq3 : sib s3=Nat.xor (selected/2^3) 1 :=
    GroupedBalancedSignUpperSelectedSiblingIndex67.index_eq s3 3 selected
      (by decide) (by omega) chosen3 start3.ready.levelWord
  intro level levelBound i
  have cases : level=0 ∨ level=1 ∨ level=2 ∨ level=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · have prior1 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.height_step_prior
        hash s1 s2 4 treeBase witnessBase 1 4 0x88000 0x83000
        start1.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
        t1 (BitVec.ofNat 64 (witnessBase+16*0+8*i.val))
        (slot_before witnessBase 1 0 i (by decide) (by omega))
    have prior2 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.height_step_prior
        hash s2 s3 4 treeBase witnessBase 2 2 0x83000 0x88000
        start2.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
        t2 (BitVec.ofNat 64 (witnessBase+16*0+8*i.val))
        (slot_before witnessBase 2 0 i (by decide) (by omega))
    have prior3 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.terminal_prior
        hash s3 built 4 treeBase witnessBase 3 0x88000 0x83000
        start3.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (Or.inr ⟨rfl,rfl⟩) t3
        (BitVec.ofNat 64 (witnessBase+16*0+8*i.val))
        (slot_before witnessBase 3 0 i (by decide) (by omega))
    rw [same,prior3,prior2,prior1]
    rw [eq0] at sib0
    simpa only [Nat.mul_zero,Nat.zero_add] using sib0 i
  · have prior2 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.height_step_prior
        hash s2 s3 4 treeBase witnessBase 2 2 0x83000 0x88000
        start2.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
        t2 (BitVec.ofNat 64 (witnessBase+16*1+8*i.val))
        (slot_before witnessBase 2 1 i (by decide) (by omega))
    have prior3 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.terminal_prior
        hash s3 built 4 treeBase witnessBase 3 0x88000 0x83000
        start3.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (Or.inr ⟨rfl,rfl⟩) t3
        (BitVec.ofNat 64 (witnessBase+16*1+8*i.val))
        (slot_before witnessBase 3 1 i (by decide) (by omega))
    rw [same,prior3,prior2]
    rw [eq1] at sib1
    simpa only [Nat.mul_one] using sib1 i
  · have prior3 :=
      GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67.terminal_prior
        hash s3 built 4 treeBase witnessBase 3 0x88000 0x83000
        start3.ready (by decide) (Or.inr rfl) witnessBound
        witnessAligned (Or.inr ⟨rfl,rfl⟩) t3
        (BitVec.ofNat 64 (witnessBase+16*2+8*i.val))
        (slot_before witnessBase 3 2 i (by decide) (by omega))
    rw [same,prior3]
    rw [eq2] at sib2
    simpa only [Nat.reduceMul] using sib2 i
  · rw [same]
    rw [eq3] at sib3
    simpa only [Nat.reduceMul] using sib3 i

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingAllData67
