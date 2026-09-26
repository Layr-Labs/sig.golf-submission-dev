import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeTickFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentTrace67
import SigGolfCandidate.TraceDeterminism

/-! A complete parent level preserves all words before the Merkle witness
base. This includes the selected WOTS signature from the preceding leaf loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev later := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState

theorem fold_before (hash : Hash) (limit source target n witnessBase : Nat)
    (s : MachineState)
    (holds : At limit source target n s)
    (small : limit≤8) (nBound : n<limit)
    (baseUpper : witnessBase≤0x80000)
    (sourceCase : source=0x83000 ∨ source=0x88000)
    (targetCase : target=0x83000 ∨ target=0x88000) :
    ∃ final : MachineState,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done limit source target final ∧
      (∀ a : Word, a.toNat<witnessBase →
        final.getMem a=s.getMem a) := by
  suffices H : ∀ remaining n (s : MachineState), remaining=limit-n →
      n<limit → At limit source target n s →
      ∃ final : MachineState,
        Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final ∧
        Done limit source target final ∧
        (∀ a : Word, a.toNat<witnessBase →
          final.getMem a=s.getMem a) by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨tick,next,last,_,_,_⟩ :=
        GroupedBalancedSignUpperTreeParentTrace67.one_tick hash limit source
          target n s holds small nBound sourceCase targetCase
      have tickFrame (a : Word) (before : a.toNat<witnessBase) :
          (later hash s).getMem a=s.getMem a :=
        GroupedBalancedSignUpperSelectedTreeTickFrame67.inner_tick_below
          hash s n target a holds.counter holds.targetPtr (by omega)
          targetCase (by omega)
      by_cases more : n+1<limit
      · obtain ⟨final,rest,done,restFrame⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (later hash s)
            (by omega) more (next more)
        refine ⟨final,?_,done,?_⟩
        · convert tick.trans rest using 1 <;> omega
        · intro a before
          exact (restFrame a before).trans (tickFrame a before)
      · have atEnd : n+1=limit := by omega
        refine ⟨later hash s,?_,last atEnd,tickFrame⟩
        have one : remaining=1 := by omega
        simpa only [one,Nat.mul_one] using tick

theorem first_level_before (hash : Hash) (s final : MachineState)
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
    (a : Word) (before : a.toNat<witnessBase) :
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
  have firstFrame (a : Word) (before : a.toNat<witnessBase) :
      (first hash s).getMem a=s.getMem a :=
    GroupedBalancedSignUpperSelectedTreeTickFrame67.first_tick_before hash
      s level witnessBase target a levelWord witness levelBound witnessBound
      targetPtr targetCase before
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
    obtain ⟨built,rest,_,restFrame⟩ := fold_before hash limit source
      target 1 witnessBase (first hash s) inv small more
      (by omega) sourceCase targetCase
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit built := by
      have countEq : 1+(limit-1)=limit := by omega
      simpa only [countEq] using firstTrace.trans rest
    have same := Trace.deterministic trace builtTrace
    rw [same]
    exact (restFrame a before).trans (firstFrame a before)
  · have one : limit=1 := by omega
    have builtTrace : Trace hash image s (113+84*(limit-1))
        (120+91*(limit-1)) limit limit (first hash s) := by
      simpa [one] using firstTrace
    have same := Trace.deterministic trace builtTrace
    rw [same]
    exact firstFrame a before

#print axioms fold_before
#print axioms first_level_before
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeParentFrame67
