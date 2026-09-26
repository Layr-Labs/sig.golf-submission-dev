import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowTick67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentTrace67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLevelTrace67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowParent67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowLevel67. -/
section
/-! Low key and public-key frame across one upper parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowParent67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev later := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState

theorem fold_low (hash : Hash) (limit source target n : Nat)
    (s : MachineState)
    (holds : At limit source target n s)
    (small : limit≤8) (nBound : n<limit)
    (sourceCase : source=0x83000 ∨ source=0x88000)
    (targetCase : target=0x83000 ∨ target=0x88000) :
    ∃ final : MachineState,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done limit source target final ∧
      (∀ a : Word, a.toNat<0x100 → final.getMem a=s.getMem a) := by
  suffices H : ∀ remaining n (s : MachineState), remaining=limit-n →
      n<limit → At limit source target n s →
      ∃ final : MachineState,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done limit source target final ∧
        (∀ a : Word, a.toNat<0x100 → final.getMem a=s.getMem a) by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨tick,next,last,_,_,_⟩ :=
        GroupedBalancedSignUpperTreeParentTrace67.one_tick hash limit source
          target n s holds small nBound sourceCase targetCase
      have tickFrame (a : Word) (low : a.toNat<0x100) :
          (later hash s).getMem a=s.getMem a :=
        GroupedBalancedSignUpperTreeLowTick67.inner_tick_low hash s n target a
          holds.counter holds.targetPtr (by omega) targetCase low
      by_cases more : n+1<limit
      · obtain ⟨final,rest,done,restFrame⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (later hash s)
            (by omega) more (next more)
        refine ⟨final,?_,done,?_⟩
        · convert tick.trans rest using 1 <;> omega
        · intro a low
          exact (restFrame a low).trans (tickFrame a low)
      · have atEnd : n+1=limit := by omega
        refine ⟨later hash s,?_,last atEnd,tickFrame⟩
        have one : remaining=1 := by omega
        simpa only [one,Nat.mul_one] using tick

theorem first_level_low (hash : Hash) (s final : MachineState)
    (level witnessBase limit source target : Nat)
    (pc : s.pc=0x1e94)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (levelBound : level<10)
    (witnessLower : 0x20060≤witnessBase)
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
    (a : Word) (low : a.toNat<0x100) :
    final.getMem a=s.getMem a := by
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases bases with ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases bases with ⟨_,h⟩ | ⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have firstTrace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    level witnessBase source target pc levelWord witness levelBound
    witnessBound witnessAligned selectedBound sourcePtr sourceCase targetPtr
    targetCase
  have firstFrame (a : Word) (low : a.toNat<0x100) :
      (first hash s).getMem a=s.getMem a :=
    GroupedBalancedSignUpperTreeLowTick67.first_tick_low hash s level
      witnessBase target a levelWord witness levelBound witnessLower
      witnessBound targetPtr targetCase low
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
    obtain ⟨built,rest,_,restFrame⟩ := fold_low hash limit source target
      1 (first hash s) inv small more sourceCase targetCase
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit built := by
      have countEq : 1+(limit-1)=limit := by omega
      simpa only [countEq] using firstTrace.trans rest
    have same := Trace.deterministic trace builtTrace
    rw [same]
    exact (restFrame a low).trans (firstFrame a low)
  · have one : limit=1 := by omega
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit (first hash s) := by
      simpa [one] using firstTrace
    have same := Trace.deterministic trace builtTrace
    rw [same]
    exact firstFrame a low

#print axioms fold_low
#print axioms first_level_low
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowParent67

end

/-! Low signer key and public-key memory survives each upper parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

private theorem ne_const (a : Word) (low : a.toNat<0x100) (b : Nat)
    (hb : 0x100≤b) (small : b<2^64) : a≠BitVec.ofNat 64 b := by
  intro eq
  have hn := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
  omega

theorem height_step_low (hash : Hash) (s next : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (positive : 0<limit) (small : limit≤8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85)
      limit limit next)
    (a : Word) (low : a.toNat<0x100) : next.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have doneLow := GroupedBalancedSignUpperTreeLowParent67.first_level_low
    hash s done height witnessBase limit source target ready.pc ready.levelWord
    ready.witness hb witnessLower hwb witnessAligned ready.selectedBound
    ready.count ready.sourcePtr ready.targetPtr bases positive small
    parentTrace a low
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
  have ne (b : Nat) (hb : 0x100≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_const a low b hb small
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
      (ne 0x81050 (by decide) (by decide))).trans doneLow)

theorem terminal_low (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (witnessLower : 0x20060≤witnessBase)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000))
    (trace : Trace hash image s 150 157 1 1 final)
    (a : Word) (low : a.toNat<0x100) : final.getMem a=s.getMem a := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have doneLow := GroupedBalancedSignUpperTreeLowParent67.first_level_low
    hash s done height witnessBase 1 source target ready.pc ready.levelWord
    ready.witness hb witnessLower hwb witnessAligned ready.selectedBound
    ready.count ready.sourcePtr ready.targetPtr bases (by decide) (by decide)
    parentTrace a low
  let shifted := step done
  have transTrace : Trace hash image done 37 37 0 0 shifted :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have builtTrace : Trace hash image s 150 157 1 1 shifted := by
    have combined := parentTrace.trans transTrace
    simpa only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using combined
  have same := Trace.deterministic trace builtTrace
  rw [same]
  have ne (b : Nat) (hb : 0x100≤b) (small : b<2^64) :
      a≠BitVec.ofNat 64 b := ne_const a low b hb small
  exact (GroupedBalancedSignBottomTreeLevelData67.frame done a
      (ne 0x810c0 (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide))).trans doneLow

#print axioms height_step_low
#print axioms terminal_low
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLowLevel67
