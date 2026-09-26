import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelProtected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeBufferParity67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllProtected67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67. -/
section
/-! All ten parent levels preserve the return slot and the H5 index words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllProtected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeAllLevels67
open GroupedBalancedSignBottomTreeParentProtected67
open GroupedBalancedSignBottomTreeLevelProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem nine_levels_protected (hash : Hash) (secretKey : SecretKey)
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
        (∀ a, Protected a → after.getMem a = s.getMem a) := by
  intro h
  induction h with
  | zero =>
      intro _
      exact ⟨s,limit,source,target,addressBase,
        by simpa [totalSteps,totalCycles,totalCalls] using
          (Trace.refl s : Trace hash image s 0 0 0 0 s),
        params,start,by simp,by simp,by intro a _; rfl⟩
  | succ h ih =>
      intro bound
      obtain ⟨mid,limitH,sourceH,targetH,addressH,first,paramsH,startH,
        sourceEq,targetEq,firstFrame⟩ := ih (by omega)
      have hBound : h < 9 := by omega
      have positive : 0 < limitH := by
        have defn := paramsH.limitDef
        rw [defn]
        interval_cases h <;> norm_num at *
      obtain ⟨next,second,paramsNext,startNext,secondFrame⟩ :=
        height_step_protected hash secretKey base h limitH sourceH targetH
          addressH mid paramsH startH hBound positive
      refine ⟨next,limitH/2,targetH,sourceH,addressH/2,?_,paramsNext,
        startNext,?_,?_,?_⟩
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

theorem ten_levels_protected (hash : Hash) (secretKey : SecretKey)
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
      (∀ a, Protected a → final.getMem a = s.getMem a) := by
  obtain ⟨at9,limit9,source9,target9,address9,first,params9,start9,
    sourceEq,targetEq,firstFrame⟩ :=
    nine_levels_protected hash secretKey base limit 0x83000 target addressBase
      s params start 9 (by decide)
  have target9Eq : target9 = 0x83000 := by simpa using targetEq
  have positive : 0 < limit9 := by rw [params9.limitDef]; decide
  obtain ⟨doneState,second,done,secondFrame⟩ :=
    one_level_protected hash secretKey base 9 limit9 source9 target9 address9
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
  refine ⟨step doneState,?_,pc,?_,?_,?_⟩
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

#print axioms ten_levels_protected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeAllProtected67

end

/-! Parent tick transitions do not modify the stack register. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem select_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeSelectPtr67.selectState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeSelectPtr67.selectState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem select_copy_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeSelectCopy67.copyState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeSelectCopy67.copyState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem pair_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreePairPtr67.pairState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreePairPtr67.pairState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem pair_loop_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreePairPtrLoop67.pairState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem children_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeChildData67.childrenState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeChildData67.childrenState,
    GroupedBalancedSignBottomTreePairLoad67.loadState,
    GroupedBalancedSignBottomTreeNodeInput67.inputState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem prelude_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeH4Prelude67.preludeState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeH4Prelude67.preludeState,
    GroupedBalancedSignBottomTreeTag67.tagState,
    GroupedBalancedSignBottomTreeHeaderMid67.middleState,
    GroupedBalancedSignBottomTreeHashReady67.readyState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem store_ptr_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem store_copy_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeHashStoreCopy67.copyState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeHashStoreCopy67.copyState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem store_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeStoreData67.storedState s).getReg .x2 =
      s.getReg .x2 := by
  exact (store_copy_sp _).trans (store_ptr_sp s)

theorem advance_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeParentAdvance67.advanceState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem branch_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeParentControl67.branchState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeParentControl67.branchState,execInstrBr]

theorem first_tick_sp (hash : Hash) (s : MachineState) :
    (GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s).getReg .x2 =
      s.getReg .x2 := by
  let selected := GroupedBalancedSignBottomTreeSelectPtr67.selectState s
  let copied := GroupedBalancedSignBottomTreeSelectCopy67.copyState selected
  let paired := GroupedBalancedSignBottomTreePairPtr67.pairState copied
  let children := GroupedBalancedSignBottomTreeChildData67.childrenState paired
  let ready := GroupedBalancedSignBottomTreeH4Prelude67.preludeState children
  let hashed := writeHash ready (hash (hashInput ready))
  let stored := GroupedBalancedSignBottomTreeStoreData67.storedState hashed
  let advanced := GroupedBalancedSignBottomTreeParentAdvance67.advanceState stored
  change (GroupedBalancedSignBottomTreeParentControl67.branchState advanced).getReg .x2 = _
  calc
    (GroupedBalancedSignBottomTreeParentControl67.branchState advanced).getReg .x2
        = advanced.getReg .x2 := branch_sp advanced
    _ = stored.getReg .x2 := advance_sp stored
    _ = hashed.getReg .x2 := store_sp hashed
    _ = ready.getReg .x2 := Keygen.hash_registers ready _ .x2
    _ = children.getReg .x2 := prelude_sp children
    _ = paired.getReg .x2 := children_sp paired
    _ = copied.getReg .x2 := pair_sp copied
    _ = selected.getReg .x2 := select_copy_sp selected
    _ = s.getReg .x2 := select_sp s

theorem inner_tick_sp (hash : Hash) (s : MachineState) :
    (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getReg .x2 =
      s.getReg .x2 := by
  let paired := GroupedBalancedSignBottomTreePairPtrLoop67.pairState s
  let children := GroupedBalancedSignBottomTreeChildData67.childrenState paired
  let ready := GroupedBalancedSignBottomTreeH4Prelude67.preludeState children
  let hashed := writeHash ready (hash (hashInput ready))
  let stored := GroupedBalancedSignBottomTreeStoreData67.storedState hashed
  let advanced := GroupedBalancedSignBottomTreeParentAdvance67.advanceState stored
  change (GroupedBalancedSignBottomTreeParentControl67.branchState advanced).getReg .x2 = _
  calc
    (GroupedBalancedSignBottomTreeParentControl67.branchState advanced).getReg .x2
        = advanced.getReg .x2 := branch_sp advanced
    _ = stored.getReg .x2 := advance_sp stored
    _ = hashed.getReg .x2 := store_sp hashed
    _ = ready.getReg .x2 := Keygen.hash_registers ready _ .x2
    _ = children.getReg .x2 := prelude_sp children
    _ = paired.getReg .x2 := children_sp paired
    _ = s.getReg .x2 := pair_loop_sp s

#print axioms first_tick_sp
#print axioms inner_tick_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67
