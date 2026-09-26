import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllLevels67

/-! The ten alternating parent levels return the root to the first buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeBufferParity67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeAllLevels67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem nine_levels_buffers (hash : Hash) (secretKey : SecretKey)
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
        targetH = (if h%2=0 then target else source) := by
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨s,limit,source,target,addressBase,
        by simpa [totalSteps,totalCycles,totalCalls] using
          (Trace.refl s : Trace hash image s 0 0 0 0 s),
        params,start,by simp,by simp⟩
  | succ h ih =>
      intro bound
      obtain ⟨mid,limitH,sourceH,targetH,addressH,first,paramsH,startH,
        sourceEq,targetEq⟩ := ih (by omega)
      have hBound : h < 9 := by omega
      have positive : 0 < limitH := by
        have defn := paramsH.limitDef
        rw [defn]
        interval_cases h <;> norm_num at *
      obtain ⟨next,second,paramsNext,startNext⟩ :=
        height_step hash secretKey base h limitH sourceH targetH addressH
          mid paramsH startH hBound positive
      refine ⟨next,limitH/2,targetH,sourceH,addressH/2,?_,paramsNext,
        startNext,?_,?_⟩
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

theorem ten_levels_fixed (hash : Hash) (secretKey : SecretKey)
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
            (64*i.val) 64) := by
  obtain ⟨at9,limit9,source9,target9,address9,first,params9,start9,
    sourceEq,targetEq⟩ :=
    nine_levels_buffers hash secretKey base limit 0x83000 target addressBase
      s params start 9 (by decide)
  have target9Eq : target9 = 0x83000 := by simpa using targetEq
  have positive : 0 < limit9 := by rw [params9.limitDef]; decide
  obtain ⟨doneState,second,done⟩ :=
    one_level hash secretKey base 9 limit9 source9 target9 address9
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
  refine ⟨step doneState,?_,pc,?_,?_⟩
  · have combined := (first.trans second).trans third
    rw [one] at combined
    simpa only [steps9,cycles9,calls9,Nat.reduceSub,Nat.reduceMul,
      Nat.reduceAdd] using combined
  · rw [target9Eq] at rootPtr
    exact rootPtr
  · intro i
    rw [target9Eq] at rootWords
    exact rootWords i

#print axioms ten_levels_fixed
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeBufferParity67
