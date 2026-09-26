import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeLevelFrame67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingLevel67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67. -/
section
/-! Inner parent ticks preserve the sibling written by the first tick. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState

theorem first_level_sibling (hash : Hash) (s final : MachineState)
    (level witnessBase limit source target : Nat)
    (sibling : Reference.Digest)
    (pc : s.pc=0x1e94)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (selectedBound : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=BitVec.ofNat 64 limit)
    (sourcePtr : s.getMem 0x810c0=BitVec.ofNat 64 source)
    (targetPtr : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (positive : 0<limit) (small : limit≤8)
    (sourceWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16*
        (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat%64)) ^^^
          (1:Word)).toNat)+8*i.val))=sibling.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s (113+84*(limit-1))
      (120+91*(limit-1)) limit limit final) :
    ∀ i : Fin 2,
      final.getMem (BitVec.ofNat 64 (witnessBase+16*level+8*i.val))=
        sibling.extractLsb' (64*i.val) 64 := by
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases bases with ⟨h,_⟩|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases bases with ⟨_,h⟩|⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have firstTrace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    level witnessBase source target pc levelWord witness levelBound
    witnessBound witnessAligned selectedBound sourcePtr sourceCase targetPtr
    targetCase
  have firstCounter : (first hash s).getMem 0x810d8=1 :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_count hash s level
      witnessBase target levelWord witness levelBound witnessBound targetPtr
      targetCase
  have firstPc := GroupedBalancedSignUpperTreeFirstControl67.tick_pc hash s
    level witnessBase target pc levelWord witness levelBound witnessBound
    targetPtr targetCase
  have frame (a : Word) (hi : 0x81000≤a.toNat)
      (lo : a.toNat<0x83000) (neD8 : a≠0x810d8)
      (ne08 : a≠0x81008) : (first hash s).getMem a=s.getMem a :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame hash s
      level witnessBase target a levelWord witness levelBound witnessBound
      targetPtr targetCase hi lo neD8 ne08
  have firstCount : (first hash s).getMem 0x810d0=
      BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact count
  have firstSource : (first hash s).getMem 0x810c0=
      BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact sourcePtr
  have firstTarget : (first hash s).getMem 0x810c8=
      BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact targetPtr
  have copied := GroupedBalancedSignUpperSelectedTreeSiblingTick67.tick_sibling
    hash s level witnessBase source target sibling levelWord witness
    levelBound witnessBound selectedBound sourcePtr sourceCase targetPtr
    targetCase sourceWords
  by_cases more : 1<limit
  · have neq : (1:Word)≠BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limit<2^64)] at hn
      have oneWord : (1:Word).toNat=1 := by decide
      rw [oneWord] at hn
      omega
    have pcNext : (first hash s).pc=0x1f08 := by
      rw [count] at firstPc
      simpa only [if_pos neq] using firstPc
    have inv : At limit source target 1 (first hash s) :=
      ⟨pcNext,firstCounter,firstCount,firstSource,firstTarget⟩
    obtain ⟨built,rest,_,restFrame⟩ :=
      GroupedBalancedSignUpperSelectedTreeParentFrame67.fold_before hash
        limit source target 1 0x80000 (first hash s) inv small more
        (by decide) sourceCase targetCase
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit built := by
      have countEq : 1+(limit-1)=limit := by omega
      simpa only [countEq] using firstTrace.trans rest
    have same := Trace.deterministic trace builtTrace
    intro i
    rw [same,restFrame _ (by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8*i.val<2^64)]
      omega)]
    exact copied i
  · have one : limit=1 := by omega
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit (first hash s) := by
      simpa [one] using firstTrace
    have same := Trace.deterministic trace builtTrace
    intro i
    rw [same]
    exact copied i

theorem first_level_prior (hash : Hash) (s final : MachineState)
    (level witnessBase limit source target : Nat)
    (pc : s.pc=0x1e94)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessBound : witnessBase+16*level+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (selectedBound : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=BitVec.ofNat 64 limit)
    (sourcePtr : s.getMem 0x810c0=BitVec.ofNat 64 source)
    (targetPtr : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (positive : 0<limit) (small : limit≤8)
    (trace : Trace hash image s (113+84*(limit-1))
      (120+91*(limit-1)) limit limit final)
    (a : Word) (before : a.toNat<witnessBase+16*level) :
    final.getMem a=s.getMem a := by
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases bases with ⟨h,_⟩|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases bases with ⟨_,h⟩|⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have firstTrace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    level witnessBase source target pc levelWord witness levelBound
    witnessBound witnessAligned selectedBound sourcePtr sourceCase targetPtr
    targetCase
  have firstFrame : (first hash s).getMem a=s.getMem a :=
    GroupedBalancedSignUpperSelectedTreeSiblingTick67.tick_prior hash s
      level witnessBase target a levelWord witness levelBound witnessBound
      targetPtr targetCase before
  have firstCounter : (first hash s).getMem 0x810d8=1 :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_count hash s level
      witnessBase target levelWord witness levelBound witnessBound targetPtr
      targetCase
  have firstPc := GroupedBalancedSignUpperTreeFirstControl67.tick_pc hash s
    level witnessBase target pc levelWord witness levelBound witnessBound
    targetPtr targetCase
  have frame (b : Word) (hi : 0x81000≤b.toNat)
      (lo : b.toNat<0x83000) (neD8 : b≠0x810d8)
      (ne08 : b≠0x81008) : (first hash s).getMem b=s.getMem b :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame hash s
      level witnessBase target b levelWord witness levelBound witnessBound
      targetPtr targetCase hi lo neD8 ne08
  have firstCount : (first hash s).getMem 0x810d0=
      BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact count
  have firstSource : (first hash s).getMem 0x810c0=
      BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact sourcePtr
  have firstTarget : (first hash s).getMem 0x810c8=
      BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact targetPtr
  by_cases more : 1<limit
  · have neq : (1:Word)≠BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limit<2^64)] at hn
      have oneWord : (1:Word).toNat=1 := by decide
      rw [oneWord] at hn
      omega
    have pcNext : (first hash s).pc=0x1f08 := by
      rw [count] at firstPc
      simpa only [if_pos neq] using firstPc
    have inv : At limit source target 1 (first hash s) :=
      ⟨pcNext,firstCounter,firstCount,firstSource,firstTarget⟩
    obtain ⟨built,rest,_,restFrame⟩ :=
      GroupedBalancedSignUpperSelectedTreeParentFrame67.fold_before hash
        limit source target 1 0x80000 (first hash s) inv small more
        (by decide) sourceCase targetCase
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit built := by
      have countEq : 1+(limit-1)=limit := by omega
      simpa only [countEq] using firstTrace.trans rest
    have same := Trace.deterministic trace builtTrace
    rw [same,restFrame a (by omega)]
    exact firstFrame
  · have one : limit=1 := by omega
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit (first hash s) := by
      simpa [one] using firstTrace
    have same := Trace.deterministic trace builtTrace
    rw [same]
    exact firstFrame

#print axioms first_level_sibling
#print axioms first_level_prior
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingLevel67

end

/-! A later Merkle level leaves already written authentication siblings intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

private theorem ne_high (a : Word) (low : a.toNat<0x80000)
    (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
    a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem height_step_prior (hash : Hash) (s next : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (positive : 0<limit) (small : limit≤8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit next)
    (a : Word) (prior : a.toNat<witnessBase+16*height) :
    next.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl|rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have donePrior :=
    GroupedBalancedSignUpperSelectedTreeSiblingLevel67.first_level_prior
      hash s done height witnessBase limit source target ready.pc
      ready.levelWord ready.witness hb hwb witnessAligned
      ready.selectedBound ready.count ready.sourcePtr ready.targetPtr bases
      positive small parentTrace a prior
  have doneLevel : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.levelWord
  have doneMax : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.maxLevel
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have shiftedPc : shifted.pc=0x1e04 := by
    have h := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc done
      heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
    rw [h]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude shifted shiftedPc
  have builtTrace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit built := by
    have combined := (parentTrace.trans transTrace).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> omega
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have low : a.toNat<0x80000 := by omega
  have ne (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_high a low b high small
  exact (preludeFrame a
    (ne 0x81008 (by decide) (by decide))
    (ne 0x81010 (by decide) (by decide))
    (ne 0x81018 (by decide) (by decide))
    (ne 0x810a8 (by decide) (by decide))
    (ne 0x810b0 (by decide) (by decide))
    (ne 0x810b8 (by decide) (by decide))).trans
    ((GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))).trans donePrior)

theorem terminal_prior (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s 150 157 1 1 final)
    (a : Word) (prior : a.toNat<witnessBase+16*height) :
    final.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl|rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have donePrior :=
    GroupedBalancedSignUpperSelectedTreeSiblingLevel67.first_level_prior
      hash s done height witnessBase 1 source target ready.pc
      ready.levelWord ready.witness hb hwb witnessAligned
      ready.selectedBound ready.count ready.sourcePtr ready.targetPtr bases
      (by decide) (by decide) parentTrace a prior
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have builtTrace : Trace hash image s 150 157 1 1 shifted := by
    have combined := parentTrace.trans transTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have low : a.toNat<0x80000 := by omega
  have ne (b : Nat) (high : 0x80000≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_high a low b high small
  exact (GroupedBalancedSignBottomTreeLevelData67.frame done a
    (ne 0x810c0 (by decide) (by decide))
    (ne 0x810c8 (by decide) (by decide))
    (ne 0x810d0 (by decide) (by decide))
    (ne 0x81000 (by decide) (by decide))
    (ne 0x81050 (by decide) (by decide))).trans donePrior

#print axioms height_step_prior
#print axioms terminal_prior
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingStepFrame67
