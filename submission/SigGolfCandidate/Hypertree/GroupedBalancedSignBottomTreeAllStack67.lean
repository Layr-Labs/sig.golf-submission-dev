import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelProtected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeBufferParity67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStackFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllStack67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStackFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeParentProtected67
open GroupedBalancedSignBottomTreeLevelProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem next_start_stack (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (done : Done hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    ∃ t,
      Trace hash image s 85 85 0 0 t ∧
      Start hash secretKey base (height+1) (limit/2) target source
        (addressBase/2) t ∧
      (∀ a, Protected a → t.getMem a = s.getMem a) ∧
      t.getReg .x2 = s.getReg .x2 := by
  obtain ⟨t,run,next,frame⟩ :=
    next_start_protected hash secretKey base height limit source target
      addressBase s params done bound
  obtain ⟨transition,between⟩ :=
    transition_continue hash secretKey base height limit source target
      addressBase s params done bound
  obtain ⟨other,prelude,_,_,_,_⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      (step s) (BitVec.ofNat 192 addressBase) between.pc between.scratch
  have constructed : Trace hash image s 85 85 0 0 other := by
    simpa only [show 37+48=85 by decide] using
      transition.trans prelude.trace
  have same := Trace.deterministic run constructed
  refine ⟨t,run,next,frame,?_⟩
  rw [same]
  exact (GroupedBalancedSignBottomTreeLevelStack67.prelude_sp
    (step s) other between.pc prelude).trans
    (GroupedBalancedSignBottomTreeLevelStack67.transition_sp s)

theorem height_step_stack (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (bound : height < 9) (positive : 0 < limit) :
    ∃ t,
      Trace hash image s
        (113+84*(limit-1)+85) (120+91*(limit-1)+85)
        limit limit t ∧
      Params base (height+1) (limit/2) target source (addressBase/2) ∧
      Start hash secretKey base (height+1) (limit/2) target source
        (addressBase/2) t ∧
      (∀ a, Protected a → t.getMem a = s.getMem a) ∧
      t.getReg .x2 = s.getReg .x2 := by
  obtain ⟨doneState,first,done,firstFrame,firstSp⟩ :=
    GroupedBalancedSignBottomTreeParentStack67.one_level_stack
      hash secretKey base height limit source target addressBase
      s params start positive
  obtain ⟨t,second,next,secondFrame,secondSp⟩ :=
    next_start_stack hash secretKey base height limit source target
      addressBase doneState params done bound
  refine ⟨t,?_,params_next base height limit source target addressBase
    params bound,next,?_,secondSp.trans firstSp⟩
  · simpa [Nat.add_assoc] using first.trans second
  · intro a safe
    exact (secondFrame a safe).trans (firstFrame a safe)

#print axioms height_step_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStackFold67

end

/-! All ten parent levels preserve the return slot and the H5 index words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeAllLevels67
open GroupedBalancedSignBottomTreeParentProtected67
open GroupedBalancedSignBottomTreeLevelProtected67
open GroupedBalancedSignBottomTreeLevelStackFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem nine_levels_stack (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase : Nat) (s : MachineState)
    (params : Params base 0 limit source target addressBase)
    (start : Start hash secretKey base 0 limit source target addressBase s) :
    ∀ h, h ≤ 9 →
      ∃ (after : MachineState) (limitH sourceH targetH addressH : Nat),
        Trace hash image s (totalSteps h) (totalCycles h)
          (totalCalls h) (totalCalls h) after ∧
        Params base h limitH sourceH targetH addressH ∧
        Start hash secretKey base h limitH sourceH targetH addressH after ∧
        sourceH = (if h%2=0 then source else target) ∧
        targetH = (if h%2=0 then target else source) ∧
        (∀ a, Protected a → after.getMem a = s.getMem a) ∧
        after.getReg .x2 = s.getReg .x2 := by
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨s,limit,source,target,addressBase,
        by simpa [totalSteps,totalCycles,totalCalls] using
          (Trace.refl s : Trace hash image s 0 0 0 0 s),
        params,start,by simp,by simp,by intro a _; rfl,rfl⟩
  | succ h ih =>
      intro bound
      obtain ⟨mid,limitH,sourceH,targetH,addressH,first,paramsH,startH,
        sourceEq,targetEq,firstFrame,firstSp⟩ := ih (by omega)
      have hBound : h < 9 := by omega
      have positive : 0 < limitH := by
        have defn := paramsH.limitDef
        rw [defn]
        interval_cases h <;> norm_num at *
      obtain ⟨next,second,paramsNext,startNext,secondFrame,secondSp⟩ :=
        height_step_stack hash secretKey base h limitH sourceH targetH
          addressH mid paramsH startH hBound positive
      refine ⟨next,limitH/2,targetH,sourceH,addressH/2,?_,paramsNext,
        startNext,?_,?_,?_,secondSp.trans firstSp⟩
      · have combined := first.trans second
        simpa only [totalSteps,totalCycles,totalCalls,stepSteps,stepCycles,
          stepCalls,←paramsH.limitDef] using combined
      · by_cases even : h%2=0
        · have oddNext : (h+1)%2=1 := by omega
          simp [oddNext,targetEq,even]
        · have odd : h%2=1 := by omega
          have evenNext : (h+1)%2=0 := by omega
          simp [evenNext,targetEq,odd]
      · by_cases even : h%2=0
        · have oddNext : (h+1)%2=1 := by omega
          simp [oddNext,sourceEq,even]
        · have odd : h%2=1 := by omega
          have evenNext : (h+1)%2=0 := by omega
          simp [evenNext,sourceEq,odd]
      · intro a safe
        exact (secondFrame a safe).trans (firstFrame a safe)

theorem ten_levels_stack (hash : Hash) (secretKey : SecretKey)
    (base limit target addressBase : Nat) (s : MachineState)
    (params : Params base 0 limit 0x83000 target addressBase)
    (start : Start hash secretKey base 0 limit 0x83000 target addressBase s) :
    ∃ final : MachineState,
      Trace hash image s 87024 94185 1023 1023 final ∧
      final.pc = 0x20ec ∧
      final.getMem 0x810c0 = 0x83000 ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x83000+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) ∧
      (∀ a, Protected a → final.getMem a = s.getMem a) ∧
      final.getReg .x2 = s.getReg .x2 ∧
      final.getMem 0x81000=10 := by
  obtain ⟨at9,limit9,source9,target9,address9,first,params9,start9,
    sourceEq,targetEq,firstFrame,firstSp⟩ :=
    nine_levels_stack hash secretKey base limit 0x83000 target addressBase
      s params start 9 (by decide)
  have target9Eq : target9 = 0x83000 := by simpa using targetEq
  have positive : 0 < limit9 := by rw [params9.limitDef]; decide
  obtain ⟨doneState,second,done,secondFrame,secondSp⟩ :=
    GroupedBalancedSignBottomTreeParentStack67.one_level_stack
      hash secretKey base 9 limit9 source9 target9 address9
      at9 params9 start9 positive
  have one : limit9=1 := by rw [params9.limitDef]; decide
  have third : Trace hash image doneState 37 37 0 0 (step doneState) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps
      doneState done.pc).trace
  have pc := terminal_pc doneState done.pc done.levelWord done.maxLevel
  obtain ⟨rootPtr,rootWords⟩ :=
    terminal_root hash secretKey base limit9 source9 target9 address9
      doneState params9 done positive
  have steps9 : totalSteps 9 = 86874 := by decide
  have cycles9 : totalCycles 9 = 94028 := by decide
  have calls9 : totalCalls 9 = 1022 := by decide
  refine ⟨step doneState,?_,pc,?_,?_,?_,?_,?_⟩
  · have combined := (first.trans second).trans third
    rw [one] at combined
    simpa only [steps9,cycles9,calls9,Nat.reduceSub,Nat.reduceMul,
      Nat.reduceAdd] using combined
  · rw [target9Eq] at rootPtr
    exact rootPtr
  · intro i
    rw [target9Eq] at rootWords
    exact rootWords i
  · intro a safe
    exact (transition_protected doneState a safe).trans
      ((secondFrame a safe).trans (firstFrame a safe))
  · exact (GroupedBalancedSignBottomTreeLevelStack67.transition_sp doneState).trans
      (secondSp.trans firstSp)
  · rw [GroupedBalancedSignBottomTreeLevelData67.height,
      done.heightWord]
    decide

#print axioms ten_levels_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllStack67
