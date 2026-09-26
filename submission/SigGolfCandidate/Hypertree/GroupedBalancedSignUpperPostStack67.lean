import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67
import SigGolfCandidate.TraceDeterminism
import SigGolfCandidate.Hypertree.KeygenCopyFrame

/-! Upper post-root bookkeeping preserves the caller stack pointer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem post_sp (s : MachineState) :
    (GroupedBalancedSignUpperPostRoot67.postState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperPostRoot67.postState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem full_sp (s : MachineState) :
    (GroupedBalancedSignUpperSelectedData67.fullState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperSelectedData67.fullState,
    GroupedBalancedSignUpperSelectedLoad67.loadState,
    GroupedBalancedSignUpperSelectedShift67.shiftState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem advance_sp (s : MachineState) :
    (GroupedBalancedSignUpperSelectedAdvance67.advanceState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperSelectedAdvance67.advanceState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem transition_sp (s : MachineState) :
    (GroupedBalancedSignUpperGroupTransition67.transitionState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperGroupTransition67.transitionState,
    GroupedBalancedSignUpperGroupTransition67.advanceLayer,
    GroupedBalancedSignUpperGroupTransition67.switchHeight,
    GroupedBalancedSignUpperGroupTransition67.finishLayer,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem selected_one_sp (s next : MachineState)
    (pc : s.pc=0x1c94)
    (trace : OrdinarySteps image s 36 next) :
    next.getReg .x2=s.getReg .x2 := by
  let mid := GroupedBalancedSignUpperSelectedData67.fullState s
  let built := GroupedBalancedSignUpperSelectedAdvance67.advanceState mid
  have a := GroupedBalancedSignUpperSelectedData67.full_steps s pc
  have midPc := GroupedBalancedSignUpperSelectedData67.full_pc s pc
  have b := GroupedBalancedSignUpperSelectedAdvance67.advance_steps mid midPc
  have constructed : OrdinarySteps image s 36 built := by
    simpa [mid,built] using Keygen.ordinary_trans image s mid built
      25 11 a b
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,advance_sp,full_sp]

theorem selected_prefix_sp (index : BitVec 192) (height : Nat)
    (hh : height=3 ∨ height=4) (start : MachineState)
    (initial : GroupedBalancedSignUpperSelectedFold67.Inv index height 0 start) :
    ∀ i, i≤height → ∀ final : MachineState,
      OrdinarySteps image start (36*i) final →
      final.getReg .x2=start.getReg .x2 := by
  intro i hi
  induction i with
  | zero =>
      intro final trace
      have same := Keygen.ordinary_deterministic trace
        (OrdinarySteps.refl start)
      rw [same]
  | succ i ih =>
      intro final trace
      obtain ⟨mid,prefixTrace,midInv,_⟩ :=
        GroupedBalancedSignUpperSelectedFold67.run_prefix index height hh
          start initial i (by omega)
      obtain ⟨next,stepTrace,_,_⟩ :=
        GroupedBalancedSignUpperSelectedFold67.one_step index height i mid
          hh midInv (by omega)
      have constructed : OrdinarySteps image start (36*(i+1)) next := by
        simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          using Keygen.ordinary_trans image start mid next
            (36*i) 36 prefixTrace stepTrace
      have same := Keygen.ordinary_deterministic trace constructed
      rw [same]
      have midPc : mid.pc=0x1c94 := by
        simpa [show i<height by omega] using midInv.2.1
      exact (selected_one_sp mid next midPc stepTrace).trans
        (ih (by omega) mid prefixTrace)

theorem selected_all_sp (index : BitVec 192) (height : Nat)
    (hh : height=3 ∨ height=4) (start final : MachineState)
    (initial : GroupedBalancedSignUpperSelectedFold67.Inv index height 0 start)
    (trace : OrdinarySteps image start (36*height) final) :
    final.getReg .x2=start.getReg .x2 :=
  selected_prefix_sp index height hh start initial height (by rfl) final trace

theorem post_group_sp (hash : Hash) (s final : MachineState)
    (index : BitVec 192) (height : Nat)
    (pc : s.pc=0x1c34)
    (valid0 : accessValid (s.getMem 0x810c0) 8=true)
    (valid8 : accessValid (s.getMem 0x810c0+8) 8=true)
    (hh : height=3 ∨ height=4)
    (limit : s.getMem 0x81060=BitVec.ofNat 64 height)
    (selected : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64)
    (trace : Trace hash image s
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      0 0 final) : final.getReg .x2=s.getReg .x2 := by
  let copied := GroupedBalancedSignUpperPostRoot67.postState s
  have copyTrace : Trace hash image s 24 24 0 0 copied :=
    OrdinarySteps.trace (hash := hash)
      (GroupedBalancedSignUpperPostRoot67.post_steps s pc valid0 valid8)
  have copyPc := GroupedBalancedSignUpperPostRoot67.post_pc s pc
  have copyWords := GroupedBalancedSignUpperPostRoot67.post_words s
    (s.getMem 0x810c0) rfl
  have copyLimit : copied.getMem 0x81060=BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s 0x81060
      (by decide) (by decide) (by decide) (by decide)]
    exact limit
  have copyIndex : ∀ w : Fin 3,
      copied.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperPostRoot67.post_frame s _
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact selected w
  have initial : GroupedBalancedSignUpperSelectedFold67.Inv index height 0 copied := by
    have hpos : 0<height := by rcases hh with rfl | rfl <;> decide
    refine ⟨by omega,by simpa [hpos] using copyPc,?_,copyLimit,?_⟩
    · exact copyWords.2.2.2
    · intro w; simpa using copyIndex w
  obtain ⟨folded,foldTrace,foldPc,_,_,foldFrame⟩ :=
    GroupedBalancedSignUpperSelectedFold67.run_all index height hh copied initial
  have shiftTrace : Trace hash image copied (36*height) (36*height) 0 0 folded :=
    OrdinarySteps.trace (hash := hash) foldTrace
  have foldedLayer : folded.getMem 0x81058=s.getMem 0x81058 := by
    rw [foldFrame 0x81058
      (by simp [GroupedBalancedSignUpperSelectedFold67.Outside]),
      GroupedBalancedSignUpperPostRoot67.post_frame s 0x81058
        (by decide) (by decide) (by decide) (by decide)]
  let built := GroupedBalancedSignUpperGroupTransition67.transitionState folded
  have moveTrace := GroupedBalancedSignUpperGroupTransition67.transition_trace
    hash folded foldPc
  have builtTrace : Trace hash image s
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      (24+36*height+
        (if s.getMem 0x81058+1=(30:Word) then 15 else 11))
      0 0 built := by
    have combined := (copyTrace.trans shiftTrace).trans moveTrace
    have exactLayer : folded.getMem (528472#64)=s.getMem (528472#64) := foldedLayer
    simpa [exactLayer,Nat.add_assoc] using combined
  have same := Trace.deterministic trace builtTrace
  rw [same,transition_sp]
  exact (selected_all_sp index height hh copied folded initial foldTrace).trans
    (post_sp s)

#print axioms post_sp
#print axioms full_sp
#print axioms advance_sp
#print axioms transition_sp
#print axioms selected_one_sp
#print axioms selected_prefix_sp
#print axioms selected_all_sp
#print axioms post_group_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostStack67
