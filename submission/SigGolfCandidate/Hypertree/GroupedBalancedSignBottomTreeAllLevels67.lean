import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelTransition67
/-! Exact ten-level signer bottom-tree trace from a first parent-level start. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllLevels67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode

def stepSteps (h : Nat) : Nat := 113+84*(512/2^h-1)+85
def stepCycles (h : Nat) : Nat := 120+91*(512/2^h-1)+85
def stepCalls (h : Nat) : Nat := 512/2^h
def totalSteps : Nat → Nat
  | 0 => 0
  | h+1 => totalSteps h + stepSteps h
def totalCycles : Nat → Nat
  | 0 => 0
  | h+1 => totalCycles h + stepCycles h
def totalCalls : Nat → Nat
  | 0 => 0
  | h+1 => totalCalls h + stepCalls h

theorem nine_levels (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase : Nat) (s : MachineState)
    (params : Params base 0 limit source target addressBase)
    (start : Start hash secretKey base 0 limit source target addressBase s) :
    ∃ (after : MachineState) (limit9 source9 target9 address9 : Nat),
      Trace hash image s (totalSteps 9) (totalCycles 9)
        (totalCalls 9) (totalCalls 9) after ∧
      Params base 9 limit9 source9 target9 address9 ∧
      Start hash secretKey base 9 limit9 source9 target9 address9 after := by
  suffices run : ∀ h, h ≤ 9 →
      ∃ (after : MachineState) (limitH sourceH targetH addressH : Nat),
        Trace hash image s (totalSteps h) (totalCycles h)
          (totalCalls h) (totalCalls h) after ∧
        Params base h limitH sourceH targetH addressH ∧
        Start hash secretKey base h limitH sourceH targetH addressH after by
    exact run 9 (by decide)
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨s,limit,source,target,addressBase,
        by simpa [totalSteps,totalCycles,totalCalls] using
          (Trace.refl s : Trace hash image s 0 0 0 0 s),params,start⟩
  | succ h ih =>
      intro bound
      obtain ⟨mid,limitH,sourceH,targetH,addressH,first,paramsH,startH⟩ :=
        ih (by omega)
      have hBound : h < 9 := by omega
      have positive : 0 < limitH := by
        have defn := paramsH.limitDef
        rw [defn]
        interval_cases h <;> norm_num at *
      obtain ⟨next,second,paramsNext,startNext⟩ :=
        height_step hash secretKey base h limitH sourceH targetH addressH
          mid paramsH startH hBound positive
      refine ⟨next,limitH/2,targetH,sourceH,addressH/2,?_,paramsNext,startNext⟩
      have combined := first.trans second
      simpa only [totalSteps,totalCycles,totalCalls,stepSteps,stepCycles,
        stepCalls,←paramsH.limitDef] using combined

theorem terminal_pc (s : MachineState)
    (donePc : s.pc = 0x2058)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 9)
    (maxLevel : s.getMem 0x81060 = 10) :
    (step s).pc = 0x20ec := by
  let swapped := GroupedBalancedSignBottomTreeLevelSwap67.swapState s
  let advanced := GroupedBalancedSignBottomTreeLevelAdvance67.advanceState swapped
  have p1 := GroupedBalancedSignBottomTreeLevelSwap67.swap_pc s donePc
  have p2 := GroupedBalancedSignBottomTreeLevelAdvance67.advance_pc swapped p1
  have regs := GroupedBalancedSignBottomTreeLevelAdvance67.advance_regs swapped
    (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)
  have witnessWord : swapped.getMem 0x81050 = BitVec.ofNat 64 9 := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81050
      (by decide) (by decide)]
    exact levelWord
  have maxWord : swapped.getMem 0x81060 = 10 := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81060
      (by decide) (by decide)]
    exact maxLevel
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState advanced).pc = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_pc advanced p2,
    regs.1,regs.2,witnessWord,maxWord]
  decide

theorem terminal_root (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase : Nat) (s : MachineState)
    (params : Params base 9 limit source target addressBase)
    (done : Done hash secretKey base 9 limit source target addressBase s)
    (positive : 0 < limit) :
    (step s).getMem 0x810c0 = BitVec.ofNat 64 target ∧
    ∀ i : Fin 2,
      (step s).getMem (BitVec.ofNat 64 (target+8*i.val)) =
        (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
          (64*i.val) 64 := by
  have one : limit=1 := by rw [params.limitDef]; decide
  have ptr : (step s).getMem 0x810c0 = BitVec.ofNat 64 target := by
    rw [GroupedBalancedSignBottomTreeLevelData67.source,done.targetPtr]
  constructor
  · exact ptr
  intro i
  have targetWord := done.targetWords 0 (by omega) i
  have wordFrame : (step s).getMem (BitVec.ofNat 64 (target+8*i.val)) =
      s.getMem (BitVec.ofNat 64 (target+8*i.val)) := by
    apply GroupedBalancedSignBottomTreeLevelData67.frame
    all_goals
      rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      fin_cases i <;> decide
  rw [wordFrame]
  change s.getMem (BitVec.ofNat 64 (target+8*i.val)) =
    (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
      (64*i.val) 64
  simpa [node,GroupedBalancedSignBottomTreeModel67.levelNode] using targetWord

theorem ten_levels (hash : Hash) (secretKey : SecretKey)
    (base limit source target addressBase : Nat) (s : MachineState)
    (params : Params base 0 limit source target addressBase)
    (start : Start hash secretKey base 0 limit source target addressBase s) :
    ∃ (final : MachineState) (rootBuffer : Nat),
      Trace hash image s 87024 94185 1023 1023 final ∧
      final.pc = 0x20ec ∧
      final.getMem 0x810c0 = BitVec.ofNat 64 rootBuffer ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (rootBuffer+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10 (base/1024)).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨at9,limit9,source9,target9,address9,first,params9,start9⟩ :=
    nine_levels hash secretKey base limit source target addressBase s params start
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
  refine ⟨step doneState,target9,?_,pc,rootPtr,rootWords⟩
  have combined := (first.trans second).trans third
  rw [one] at combined
  simpa only [steps9,cycles9,calls9,Nat.reduceSub,Nat.reduceMul,
    Nat.reduceAdd] using combined

#print axioms nine_levels
#print axioms terminal_pc
#print axioms terminal_root
#print axioms ten_levels
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllLevels67
