import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomPathFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelTransition67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllLevels67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTransition67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedLevels67. -/
section
/-! The bottom-tree level transition leaves all completed sibling words intact. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTransition67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomPathFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

private theorem safe_ne (a : Word) (safe : Safe a) (b : Nat)
    (lower : 0x80000 ≤ b) (upper : b < 0x90000)
    (other : b ≠ 0x810e8) : a ≠ BitVec.ofNat 64 b := by
  rcases safe with low | rfl
  · intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have selfNat : (0x810e8 : Word).toNat = 0x810e8 := by decide
    rw [selfNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    exact other hn.symm

theorem next_start_safe (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (done : Done hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    ∃ t,
      Trace hash image s 85 85 0 0 t ∧
      Start hash secretKey base (height+1) (limit/2) target source
        (addressBase/2) t ∧
      (∀ a, Safe a → t.getMem a = s.getMem a) := by
  obtain ⟨t,run,next⟩ :=
    next_start hash secretKey base height limit source target addressBase
      s params done bound
  obtain ⟨transition,between⟩ :=
    transition_continue hash secretKey base height limit source target
      addressBase s params done bound
  obtain ⟨other,prelude,_,_,_,frame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      (step s) (BitVec.ofNat 192 addressBase) between.pc between.scratch
  have constructed : Trace hash image s 85 85 0 0 other := by
    simpa only [show 37+48=85 by decide] using
      transition.trans prelude.trace
  have same := Trace.deterministic run constructed
  refine ⟨t,run,next,?_⟩
  intro a safe
  rw [same]
  have ne (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 0x90000)
      (other : b ≠ 0x810e8) : a ≠ BitVec.ofNat 64 b :=
    safe_ne a safe b lower upper other
  have preludeFrame : other.getMem a = (step s).getMem a :=
    frame a
      (ne 0x81008 (by decide) (by decide) (by decide))
      (ne 0x81010 (by decide) (by decide) (by decide))
      (ne 0x81018 (by decide) (by decide) (by decide))
      (ne 0x810a8 (by decide) (by decide) (by decide))
      (ne 0x810b0 (by decide) (by decide) (by decide))
      (ne 0x810b8 (by decide) (by decide) (by decide))
  have stepFrame : (step s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeLevelData67.frame s a
      (ne 0x810c0 (by decide) (by decide) (by decide))
      (ne 0x810c8 (by decide) (by decide) (by decide))
      (ne 0x810d0 (by decide) (by decide) (by decide))
      (ne 0x81000 (by decide) (by decide) (by decide))
      (ne 0x81050 (by decide) (by decide) (by decide))
  exact preludeFrame.trans stepFrame

#print axioms next_start_safe
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedTransition67

end

/-! All ten bottom-tree siblings persist to the upper-tree entry point. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedLevels67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeAllLevels67
open GroupedBalancedSignBottomPathFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

def pathSlot (level : Nat) (i : Fin 2) : Word :=
  BitVec.ofNat 64 (0x20090+16*level+8*i.val)

def siblingNode (hash : Hash) (secretKey : SecretKey)
    (base selectedIndex level : Nat) : Reference.Digest :=
  GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey base level
    (Nat.xor (selectedIndex/2^level) 1)

private theorem path_slot_lt (level h : Nat) (i : Fin 2)
    (levelLt : level < h) (hBound : h ≤ 10) :
    (pathSlot level i).toNat < 0x20090+16*h := by
  unfold pathSlot
  have hi := i.isLt
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

private theorem path_slot_safe (level : Nat) (i : Fin 2)
    (bound : level < 10) : Safe (pathSlot level i) := by
  left
  have h := path_slot_lt level 10 i bound (by decide)
  omega

theorem nine_levels_selected (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase selectedIndex : Nat)
    (s : MachineState)
    (params : Params base 0 limit source target addressBase)
    (start : Start hash secretKey base 0 limit source target addressBase s)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex) :
    ∀ h, h ≤ 9 →
      ∃ (after : MachineState) (limitH sourceH targetH addressH : Nat),
        Trace hash image s (totalSteps h) (totalCycles h)
          (totalCalls h) (totalCalls h) after ∧
        Params base h limitH sourceH targetH addressH ∧
        Start hash secretKey base h limitH sourceH targetH addressH after ∧
        (after.getMem 0x810e8).toNat = selectedIndex ∧
        (∀ a : Word, a.toNat < 0x20090 → after.getMem a = s.getMem a) ∧
        (∀ level, level < h → ∀ i : Fin 2,
          after.getMem (pathSlot level i) =
            (siblingNode hash secretKey base selectedIndex level).extractLsb'
              (64*i.val) 64) := by
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨s,limit,source,target,addressBase,
        by simpa [totalSteps,totalCycles,totalCalls] using
          (Trace.refl s : Trace hash image s 0 0 0 0 s),
        params,start,selectedWord,by intro a _; rfl,
        by intro level impossible; omega⟩
  | succ h ih =>
      intro bound
      obtain ⟨mid,limitH,sourceH,targetH,addressH,first,paramsH,startH,
        selectedH,lowFrame,earlier⟩ := ih (by omega)
      have hBound : h < 9 := by omega
      have positive : 0 < limitH := by
        have defn := paramsH.limitDef
        rw [defn]
        interval_cases h <;> norm_num at *
      obtain ⟨doneState,levelTrace,done,priorFrame,selectedFrame,sibling⟩ :=
        GroupedBalancedSignBottomPathFold67.one_level_selected
          hash secretKey base h limitH sourceH targetH addressH selectedIndex
          mid paramsH startH positive selectedH
      obtain ⟨next,nextTrace,nextStart,nextSafe⟩ :=
        GroupedBalancedSignBottomSelectedTransition67.next_start_safe
          hash secretKey base h limitH sourceH targetH addressH doneState
          paramsH done hBound
      refine ⟨next,limitH/2,targetH,sourceH,addressH/2,?_,
        params_next base h limitH sourceH targetH addressH paramsH hBound,
        nextStart,?_,?_,?_⟩
      · have combined := (first.trans levelTrace).trans nextTrace
        simpa only [totalSteps,totalCycles,totalCalls,stepSteps,stepCycles,
          stepCalls,←paramsH.limitDef,Nat.add_assoc,Nat.add_zero] using combined
      · rw [nextSafe 0x810e8 (Or.inr rfl),selectedFrame]
        exact selectedH
      · intro a ha
        exact (nextSafe a (Or.inl (by omega))).trans
          ((priorFrame a (by omega)).trans (lowFrame a ha))
      · intro level levelBound i
        have safe : Safe (pathSlot level i) :=
          path_slot_safe level i (by omega)
        rw [nextSafe _ safe]
        by_cases prior : level < h
        · have before := path_slot_lt level h i prior (by omega)
          rw [priorFrame _ before]
          exact earlier level prior i
        · have equal : level=h := by omega
          subst level
          simpa [pathSlot,siblingNode] using sibling i

private theorem terminal_below (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (step s).getMem a = s.getMem a := by
  have ne (b : Nat) (hb : 0x80000 ≤ b) (upper : b < 2^64) :
      a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at hn
    omega
  exact GroupedBalancedSignBottomTreeLevelData67.frame s a
    (ne 0x810c0 (by decide) (by decide))
    (ne 0x810c8 (by decide) (by decide))
    (ne 0x810d0 (by decide) (by decide))
    (ne 0x81000 (by decide) (by decide))
    (ne 0x81050 (by decide) (by decide))

theorem ten_levels_selected (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase selectedIndex : Nat)
    (s : MachineState)
    (params : Params base 0 limit source target addressBase)
    (start : Start hash secretKey base 0 limit source target addressBase s)
    (selectedWord : (s.getMem 0x810e8).toNat = selectedIndex) :
    ∃ (final : MachineState) (rootBuffer : Nat),
      Trace hash image s 87024 94185 1023 1023 final ∧
      final.pc = 0x20ec ∧
      final.getMem 0x810c0 = BitVec.ofNat 64 rootBuffer ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (rootBuffer+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) ∧
      (∀ a : Word, a.toNat < 0x20090 → final.getMem a = s.getMem a) ∧
      (∀ level, level < 10 → ∀ i : Fin 2,
        final.getMem (pathSlot level i) =
          (siblingNode hash secretKey base selectedIndex level).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨at9,limit9,source9,target9,address9,first,params9,start9,
    selected9,low9,path9⟩ :=
    nine_levels_selected hash secretKey base limit source target addressBase
      selectedIndex s params start selectedWord 9 (by decide)
  have positive : 0 < limit9 := by rw [params9.limitDef]; decide
  obtain ⟨doneState,second,done,priorFrame,_,sibling9⟩ :=
    GroupedBalancedSignBottomPathFold67.one_level_selected
      hash secretKey base 9 limit9 source9 target9 address9 selectedIndex
      at9 params9 start9 positive selected9
  have one : limit9=1 := by rw [params9.limitDef]; decide
  have third : Trace hash image doneState 37 37 0 0 (step doneState) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps
      doneState done.pc).trace
  have pc := GroupedBalancedSignBottomTreeAllLevels67.terminal_pc
    doneState done.pc done.levelWord done.maxLevel
  obtain ⟨rootPtr,rootWords⟩ :=
    GroupedBalancedSignBottomTreeAllLevels67.terminal_root
      hash secretKey base limit9 source9 target9 address9 doneState
      params9 done positive
  have steps9 : totalSteps 9=86874 := by decide
  have cycles9 : totalCycles 9=94028 := by decide
  have calls9 : totalCalls 9=1022 := by decide
  refine ⟨step doneState,target9,?_,pc,rootPtr,rootWords,?_,?_⟩
  · have combined := (first.trans second).trans third
    rw [one] at combined
    simpa only [steps9,cycles9,calls9,Nat.reduceSub,Nat.reduceMul,
      Nat.reduceAdd] using combined
  · intro a ha
    exact (terminal_below doneState a (by omega)).trans
      ((priorFrame a (by omega)).trans (low9 a ha))
  · intro level levelBound i
    have safe : (pathSlot level i).toNat < 0x80000 := by
      have lt := path_slot_lt level 10 i levelBound (by decide)
      omega
    rw [terminal_below doneState _ safe]
    by_cases prior : level<9
    · have before := path_slot_lt level 9 i prior (by decide)
      rw [priorFrame _ before]
      exact path9 level prior i
    · have equal : level=9 := by omega
      subst level
      simpa [pathSlot,siblingNode] using sibling9 i

#print axioms nine_levels_selected
#print axioms ten_levels_selected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedLevels67
