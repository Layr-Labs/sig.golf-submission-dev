import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeRegion67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCalleeRoot67

/-! Prefix-region certificate for the reused upper Merkle signer callee. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeBelow67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignImageTransfer67
open GroupedBalancedSignUpperTreeRegion67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem trace_end_unique {hash : Hash} {s t u : MachineState}
    {steps cycles calls blocks cycles' calls' blocks' : Nat}
    (first : Trace hash image s steps cycles calls blocks t)
    (second : Trace hash image s steps cycles' calls' blocks' u) : t=u := by
  induction first generalizing cycles' calls' blocks' u with
  | refl state =>
      cases second with
      | refl => rfl
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      cases second with
      | ordinary state other u otherInstruction _ _ _ _ hf' hs' rest =>
          have instructionEq : instruction = otherInstruction :=
            Option.some.inj (hf.symm.trans hf')
          subst otherInstruction
          have nextEq : next = other := Option.some.inj (hs.symm.trans hs')
          subst other
          exact ih rest
      | hash state u _ _ _ _ hf' _ _ _ =>
          have eq : instruction = .base .ECALL :=
            Option.some.inj (hf.symm.trans hf')
          subst instruction
          simp [ordinaryStep] at hs
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      cases second with
      | ordinary state other u otherInstruction _ _ _ _ hf' hs' rest =>
          have instructionEq : Instruction.base Instr.ECALL = otherInstruction :=
            Option.some.inj (hf.symm.trans hf')
          subst otherInstruction
          simp [ordinaryStep] at hs'
      | hash state u _ _ _ _ hf' hs' hv' rest =>
          exact ih rest

theorem inner_tick_below (hash : Hash) (limit source target n : Nat)
    (s : MachineState)
    (holds : GroupedBalancedSignUpperTreeParentTrace67.At limit source target n s)
    (small : limit ≤ 8) (nBound : n < limit)
    (sourceCase : source = 0x83000 ∨ source = 0x88000)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    ∃ trace : Trace hash image s 84 91 1 1
        (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s),
      TraceBelow hash trace := by
  obtain ⟨trace,_,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.one_tick hash limit source target n s
      holds small nBound sourceCase targetCase
  refine ⟨trace, trace_below_len trace ?_ ?_⟩
  · rw [holds.pc]
    decide
  · rw [holds.pc]
    decide

theorem inner_fold_below (hash : Hash) (limit source target n : Nat)
    (s : MachineState)
    (holds : GroupedBalancedSignUpperTreeParentTrace67.At limit source target n s)
    (small : limit ≤ 8) (nBound : n < limit)
    (sourceCase : source = 0x83000 ∨ source = 0x88000)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    ∃ final : MachineState,
      ∃ trace : Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final,
      TraceBelow hash trace ∧
      GroupedBalancedSignUpperTreeParentTrace67.Done limit source target final := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → GroupedBalancedSignUpperTreeParentTrace67.At limit source target n s →
      ∃ final,
        ∃ trace : Trace hash image s (84*remaining) (91*remaining)
          remaining remaining final,
        TraceBelow hash trace ∧
        GroupedBalancedSignUpperTreeParentTrace67.Done limit source target final by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      let next := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s
      obtain ⟨tick,nextAt,last,_,_,_⟩ :=
        GroupedBalancedSignUpperTreeParentTrace67.one_tick hash limit source target n s
          holds small nBound sourceCase targetCase
      have tickBelow : TraceBelow hash tick :=
        trace_below_len tick (by rw [holds.pc]; decide)
          (by rw [holds.pc]; decide)
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,restBelow,done⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) next
            (by omega) more (nextAt more)
        have heq : remaining = 1+(limit-(n+1)) := by omega
        subst remaining
        refine ⟨final,?_⟩
        have combined := tick.trans rest
        have combinedBelow := TraceBelow.trans tick rest tickBelow restBelow
        have hsteps : 84*(1+(limit-(n+1))) = 84+84*(limit-(n+1)) := by omega
        have hcycles : 91*(1+(limit-(n+1))) = 91+91*(limit-(n+1)) := by omega
        rw [heq,hsteps,hcycles]
        exact ⟨combined,combinedBelow,done⟩
      · have atEnd : n+1=limit := by omega
        have one : remaining=1 := by omega
        subst remaining
        refine ⟨next,?_⟩
        have countOne : limit-n=1 := by omega
        simpa only [countOne,Nat.mul_one] using
          (show ∃ trace : Trace hash image s 84 91 1 1 next,
            TraceBelow hash trace ∧
              GroupedBalancedSignUpperTreeParentTrace67.Done limit source target next
            from ⟨tick,tickBelow,last atEnd⟩)

theorem below_of_same {hash : Hash} {s t u : MachineState}
    {steps cycles calls blocks : Nat}
    (old : Trace hash image s steps cycles calls blocks t)
    (fresh : Trace hash image s steps cycles calls blocks u)
    (freshBelow : TraceBelow hash fresh) : TraceBelow hash old := by
  have endpoints : t=u := trace_end_unique old fresh
  subst u
  have proofs : fresh=old := Subsingleton.elim _ _
  simpa only [proofs] using freshBelow

theorem first_level_below (hash : Hash) (s final : MachineState)
    (level witnessBase limit source target : Nat)
    (trace : Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
      limit limit final)
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
    (positive : 0<limit) (small : limit≤8) :
    TraceBelow hash trace := by
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases bases with ⟨h,_⟩ | ⟨h,_⟩ <;> simp [h]
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases bases with ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
  let first := GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s
  have firstTrace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    level witnessBase source target pc levelWord witness levelBound
    witnessBound witnessAligned selectedBound sourcePtr sourceCase targetPtr targetCase
  have firstBelow : TraceBelow hash firstTrace :=
    trace_below_len firstTrace (by rw [pc]; decide) (by rw [pc]; decide)
  have firstCounter : first.getMem 0x810d8=1 :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_count hash s level
      witnessBase target levelWord witness levelBound witnessBound targetPtr targetCase
  have firstPc := GroupedBalancedSignUpperTreeFirstControl67.tick_pc hash s
    level witnessBase target pc levelWord witness levelBound witnessBound
    targetPtr targetCase
  have frame (a : Word) (hi : 0x81000≤a.toNat) (lo : a.toNat<0x83000)
      (neCounter : a≠0x810d8) (neAddr : a≠0x81008) :
      first.getMem a=s.getMem a :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame hash s
      level witnessBase target a levelWord witness levelBound witnessBound
      targetPtr targetCase hi lo neCounter neAddr
  have firstCount : first.getMem 0x810d0=BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact count
  have firstSource : first.getMem 0x810c0=BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact sourcePtr
  have firstTarget : first.getMem 0x810c8=BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact targetPtr
  by_cases more : 1<limit
  · have neq : (1:Word) ≠ BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limit<2^64)] at hn
      have oneWord : (1:Word).toNat=1 := by decide
      rw [oneWord] at hn
      omega
    have pcNext : first.pc=0x1f08 := by
      rw [count] at firstPc
      simpa only [if_pos neq] using firstPc
    have inv : GroupedBalancedSignUpperTreeParentTrace67.At
        limit source target 1 first :=
      ⟨pcNext,firstCounter,firstCount,firstSource,firstTarget⟩
    obtain ⟨other,rest,restBelow,_⟩ := inner_fold_below hash limit source target 1
      first inv small more sourceCase targetCase
    have bundled : ∃ fresh : Trace hash image s
        (113+84*(limit-1)) (120+91*(limit-1)) limit limit other,
        TraceBelow hash fresh := by
      have countEq : 1+(limit-1)=limit := by omega
      simpa only [countEq] using
        (show ∃ fresh : Trace hash image s
            (113+84*(limit-1)) (120+91*(limit-1))
            (1+(limit-1)) (1+(limit-1)) other,
          TraceBelow hash fresh from
            ⟨firstTrace.trans rest,
              TraceBelow.trans firstTrace rest firstBelow restBelow⟩)
    obtain ⟨fresh,freshBelow⟩ := bundled
    exact below_of_same trace fresh freshBelow
  · have one : limit=1 := by omega
    have bundled : ∃ fresh : Trace hash image s
        (113+84*(limit-1)) (120+91*(limit-1)) limit limit first,
        TraceBelow hash fresh := by
      simpa [one] using
        (show ∃ fresh : Trace hash image s 113 120 1 1 first,
          TraceBelow hash fresh from ⟨firstTrace,firstBelow⟩)
    obtain ⟨fresh,freshBelow⟩ := bundled
    exact below_of_same trace fresh freshBelow

theorem height_step_below (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (trace : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85) limit limit final)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1<heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax<2^64)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (positive : 0<limit) (small : limit≤8)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000)) :
    TraceBelow hash trace := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have parentBelow := first_level_below hash s done height witnessBase
    limit source target parentTrace ready.pc ready.levelWord ready.witness
    hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
    ready.targetPtr bases positive small
  let step := GroupedBalancedSignBottomTreeLevelControl67.transitionState done
  have transitionTrace : Trace hash image done 37 37 0 0 step :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have transitionBelow : TraceBelow hash transitionTrace :=
    trace_below_len transitionTrace (by rw [doneInv.pc]; decide)
      (by rw [doneInv.pc]; decide)
  have doneLevel : done.getMem 0x81050=BitVec.ofNat 64 height := by
    rw [parentFrame 0x81050 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.levelWord
  have doneMax : done.getMem 0x81060=BitVec.ofNat 64 heightMax := by
    rw [parentFrame 0x81060 ⟨by decide,by decide,by decide,by decide⟩]
    exact ready.maxLevel
  have pcStep : step.pc=0x1e04 := by
    have hp := GroupedBalancedSignUpperTreeLevelTrace67.transition_pc done
      heightMax height doneInv.pc doneLevel doneMax (by omega) maxBound
    simpa [step, Nat.ne_of_lt heightBound] using hp
  obtain ⟨after,prelude,_,_⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude step pcStep
  have preludeTrace : Trace hash image step 48 48 0 0 after := prelude.trace
  have preludeBelow : TraceBelow hash preludeTrace :=
    trace_below_len preludeTrace (by rw [pcStep]; decide)
      (by rw [pcStep]; decide)
  have raw : ∃ fresh : Trace hash image s
      ((113+84*(limit-1))+37+48) ((120+91*(limit-1))+37+48)
      ((limit+0)+0) ((limit+0)+0) after,
      TraceBelow hash fresh :=
    ⟨(parentTrace.trans transitionTrace).trans preludeTrace,
      TraceBelow.trans _ _ (TraceBelow.trans _ _ parentBelow transitionBelow)
        preludeBelow⟩
  have stepEq : (113+84*(limit-1))+37+48 = 113+84*(limit-1)+85 := by omega
  have cycleEq : (120+91*(limit-1))+37+48 = 120+91*(limit-1)+85 := by omega
  have bundled : ∃ fresh : Trace hash image s
      (113+84*(limit-1)+85) (120+91*(limit-1)+85) limit limit after,
      TraceBelow hash fresh := by
    simpa only [stepEq,cycleEq,Nat.add_zero] using raw
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem terminal_below (hash : Hash) (s final : MachineState)
    (heightMax treeBase witnessBase height source target : Nat)
    (trace : Trace hash image s 150 157 1 1 final)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      heightMax treeBase witnessBase height 1 source target s)
    (terminalHeight : height+1=heightMax)
    (maxBound : heightMax=3 ∨ heightMax=4)
    (treeBound : treeBase+heightMax<2^64)
    (witnessBound : witnessBase+16*heightMax+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (bases : (source=0x83000 ∧ target=0x88000) ∨
      (source=0x88000 ∧ target=0x83000)) :
    TraceBelow hash trace := by
  have hb : height<10 := by rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16≤0x80000 := by omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase 1 source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases (by decide) (by decide)
  have parentBelow := first_level_below hash s done height witnessBase
    1 source target parentTrace ready.pc ready.levelWord ready.witness
    hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
    ready.targetPtr bases (by decide) (by decide)
  let step := GroupedBalancedSignBottomTreeLevelControl67.transitionState done
  have transitionTrace : Trace hash image done 37 37 0 0 step :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  have transitionBelow : TraceBelow hash transitionTrace :=
    trace_below_len transitionTrace (by rw [doneInv.pc]; decide)
      (by rw [doneInv.pc]; decide)
  have raw : ∃ fresh : Trace hash image s (113+37) (120+37)
      (1+0) (1+0) step,
      TraceBelow hash fresh :=
    ⟨parentTrace.trans transitionTrace,
      TraceBelow.trans _ _ parentBelow transitionBelow⟩
  have bundled : ∃ fresh : Trace hash image s 150 157 1 1 step,
      TraceBelow hash fresh := by simpa only [Nat.reduceAdd,Nat.add_zero] using raw
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem all_height3_below (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 882 931 7 7 final)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      3 treeBase witnessBase 0 4 0x83000 0x88000 s)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    TraceBelow hash trace := by
  open GroupedBalancedSignUpperTreeLevelTrace67 in
    obtain ⟨at1,t0,ready1,_,_⟩ := height_step hash s 3 treeBase witnessBase
      0 4 0x83000 0x88000 ready (by decide) (Or.inl rfl) treeBound
      witnessBound witnessAligned (by decide) (by decide)
      (Or.inl ⟨rfl,rfl⟩)
  have b0 := height_step_below hash s at1 3 treeBase witnessBase
    0 4 0x83000 0x88000 t0 ready (by decide) (Or.inl rfl)
    treeBound witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,ready2,_,_⟩ :=
    GroupedBalancedSignUpperTreeLevelTrace67.height_step hash at1 3 treeBase
      witnessBase 1 2 0x88000 0x83000
      (by simpa only [show 4/2=2 by decide] using ready1)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  have b1 := height_step_below hash at1 at2 3 treeBase witnessBase
    1 2 0x88000 0x83000 t1
    (by simpa only [show 4/2=2 by decide] using ready1)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨terminal,t2,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at2 3 treeBase
      witnessBase 2 0x83000 0x88000
      (by simpa only [show 2/2=1 by decide] using ready2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (Or.inl ⟨rfl,rfl⟩)
  have b2 := terminal_below hash at2 terminal 3 treeBase witnessBase
    2 0x83000 0x88000 t2
    (by simpa only [show 2/2=1 by decide] using ready2)
    (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
    (Or.inl ⟨rfl,rfl⟩)
  have combined := (t0.trans t1).trans t2
  have combinedBelow := TraceBelow.trans _ _
    (TraceBelow.trans _ _ b0 b1) b2
  have bundled : ∃ fresh : Trace hash image s 882 931 7 7 terminal,
      TraceBelow hash fresh := by
    convert (show ∃ fresh : Trace hash image s
      (113+84*(4-1)+85 + (113+84*(2-1)+85) + 150)
      (120+91*(4-1)+85 + (120+91*(2-1)+85) + 157)
      (4+2+1) (4+2+1) terminal,
      TraceBelow hash fresh from ⟨combined,combinedBelow⟩) using 1 <;> decide
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem all_height4_below (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 1668 1773 15 15 final)
    (ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready
      4 treeBase witnessBase 0 8 0x83000 0x88000 s)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    TraceBelow hash trace := by
  obtain ⟨at1,t0,ready1,_,_⟩ :=
    GroupedBalancedSignUpperTreeLevelTrace67.height_step hash s 4 treeBase witnessBase
      0 8 0x83000 0x88000 ready (by decide) (Or.inr rfl) treeBound
      witnessBound witnessAligned (by decide) (by decide)
      (Or.inl ⟨rfl,rfl⟩)
  have b0 := height_step_below hash s at1 4 treeBase witnessBase
    0 8 0x83000 0x88000 t0 ready (by decide) (Or.inr rfl)
    treeBound witnessBound witnessAligned (by decide) (by decide)
    (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨at2,t1,ready2,_,_⟩ :=
    GroupedBalancedSignUpperTreeLevelTrace67.height_step hash at1 4 treeBase
      witnessBase 1 4 0x88000 0x83000
      (by simpa only [show 8/2=4 by decide] using ready1)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  have b1 := height_step_below hash at1 at2 4 treeBase witnessBase
    1 4 0x88000 0x83000 t1
    (by simpa only [show 8/2=4 by decide] using ready1)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨at3,t2,ready3,_,_⟩ :=
    GroupedBalancedSignUpperTreeLevelTrace67.height_step hash at2 4 treeBase
      witnessBase 2 2 0x83000 0x88000
      (by simpa only [show 4/2=2 by decide] using ready2)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  have b2 := height_step_below hash at2 at3 4 treeBase witnessBase
    2 2 0x83000 0x88000 t2
    (by simpa only [show 4/2=2 by decide] using ready2)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (by decide) (by decide) (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨terminal,t3,_,_,_,_⟩ :=
    GroupedBalancedSignUpperTreeTerminalTrace67.terminal hash at3 4 treeBase
      witnessBase 3 0x88000 0x83000
      (by simpa only [show 2/2=1 by decide] using ready3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (Or.inr ⟨rfl,rfl⟩)
  have b3 := terminal_below hash at3 terminal 4 treeBase witnessBase
    3 0x88000 0x83000 t3
    (by simpa only [show 2/2=1 by decide] using ready3)
    (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
    (Or.inr ⟨rfl,rfl⟩)
  have combined := ((t0.trans t1).trans t2).trans t3
  have combinedBelow := TraceBelow.trans _ _
    (TraceBelow.trans _ _ (TraceBelow.trans _ _ b0 b1) b2) b3
  have bundled : ∃ fresh : Trace hash image s 1668 1773 15 15 terminal,
      TraceBelow hash fresh := by
    convert (show ∃ fresh : Trace hash image s
      (113+84*(8-1)+85 + (113+84*(4-1)+85) + (113+84*(2-1)+85) + 150)
      (120+91*(8-1)+85 + (120+91*(4-1)+85) + (120+91*(2-1)+85) + 157)
      (8+4+2+1) (8+4+2+1) terminal,
      TraceBelow hash fresh from ⟨combined,combinedBelow⟩) using 1 <;> decide
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem start_below (hash : Hash) (s final : MachineState)
    (trace : Trace hash image s 72 72 0 0 final)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700) :
    TraceBelow hash trace := by
  let called := GroupedBalancedSignUpperTreeCall67.called s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let initialized := GroupedBalancedSignBottomTreeInit67.initState entered
  have callSteps := GroupedBalancedSignUpperTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignUpperTreeCall67.call_pc s pc
  have calledSp : called.getReg .x2=0xfff7e0 ∨ called.getReg .x2=0xfff700 := by
    rw [GroupedBalancedSignUpperTreeCall67.call_sp]
    exact sp
  have entrySteps := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc calledSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initSteps := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  obtain ⟨after,prelude,_,_⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude initialized initPc
  have callBelow : TraceBelow hash (callSteps.trace (hash := hash)) := by
    have code : fetch image s = some (.base (.JAL .x1 0x178)) := by
      simp only [Keygen.fetch_at,pc]
      decide
    exact TraceBelow.ordinary s called called (.base (.JAL .x1 0x178))
      0 0 0 0 code rfl (Trace.refl called) (by rw [pc]; decide)
      (by rw [pc]; decide) (TraceBelow.refl called)
  have entryTrace : Trace hash image called 6 6 0 0 entered := entrySteps.trace
  have entryBelow : TraceBelow hash entryTrace :=
    trace_below_len entryTrace (by rw [callPc]; decide)
      (by rw [callPc]; decide)
  have initTrace : Trace hash image entered 17 17 0 0 initialized := initSteps.trace
  have initBelow : TraceBelow hash initTrace :=
    trace_below_len initTrace (by rw [entryPc]; decide)
      (by rw [entryPc]; decide)
  have preludeTrace : Trace hash image initialized 48 48 0 0 after := prelude.trace
  have preludeBelow : TraceBelow hash preludeTrace :=
    trace_below_len preludeTrace (by rw [initPc]; decide)
      (by rw [initPc]; decide)
  have combined := (((callSteps.trace (hash := hash)).trans entryTrace).trans
    initTrace).trans preludeTrace
  have combinedBelow := TraceBelow.trans _ _
    (TraceBelow.trans _ _ (TraceBelow.trans _ _ callBelow entryBelow) initBelow)
    preludeBelow
  have bundled : ∃ fresh : Trace hash image s 72 72 0 0 after,
      TraceBelow hash fresh := by
    convert (show ∃ fresh : Trace hash image s
      (1+6+17+48) (1+6+17+48) (((0+0)+0)+0) (((0+0)+0)+0) after,
      TraceBelow hash fresh from ⟨combined,combinedBelow⟩) using 1 <;> decide
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem return_below (hash : Hash) (s final : MachineState)
    (trace : Trace hash image s 3 3 0 0 final)
    (pc : s.pc=0x20ec) : TraceBelow hash trace :=
  trace_below_len trace (by rw [pc]; decide) (by rw [pc]; decide)

theorem callee_height3_below (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 957 1006 7 7 final)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=8)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) : TraceBelow hash trace := by
  obtain ⟨ready,startTrace,readyInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 3 treeBase witnessBase 4
      pc sp tree maxLevel witness selected count (by decide)
  have startBelow := start_below hash s ready startTrace pc sp
  obtain ⟨root,parentTrace,rootPc,_,rootSp,rootHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height3 hash ready treeBase
      witnessBase readyInv treeBound witnessBound witnessAligned
  have parentBelow := all_height3_below hash ready root treeBase witnessBase
    parentTrace readyInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready root
      sp slot readySp rootSp rootHigh rootPc
  have returnBelow := return_below hash root (Keygen.returnState root)
    returnTrace rootPc
  have combined := (startTrace.trans parentTrace).trans returnTrace
  have combinedBelow := TraceBelow.trans _ _
    (TraceBelow.trans _ _ startBelow parentBelow) returnBelow
  have bundled : ∃ fresh : Trace hash image s 957 1006 7 7
      (Keygen.returnState root), TraceBelow hash fresh := by
    convert (show ∃ fresh : Trace hash image s
      (72+882+3) (72+931+3) ((0+7)+0) ((0+7)+0)
      (Keygen.returnState root), TraceBelow hash fresh from
        ⟨combined,combinedBelow⟩) using 1 <;> decide
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

theorem callee_height4_below (hash : Hash) (s final : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 1743 1848 15 15 final)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=16)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) : TraceBelow hash trace := by
  obtain ⟨ready,startTrace,readyInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 4 treeBase witnessBase 8
      pc sp tree maxLevel witness selected count (by decide)
  have startBelow := start_below hash s ready startTrace pc sp
  obtain ⟨root,parentTrace,rootPc,_,rootSp,rootHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height4 hash ready treeBase
      witnessBase readyInv treeBound witnessBound witnessAligned
  have parentBelow := all_height4_below hash ready root treeBase witnessBase
    parentTrace readyInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready root
      sp slot readySp rootSp rootHigh rootPc
  have returnBelow := return_below hash root (Keygen.returnState root)
    returnTrace rootPc
  have combined := (startTrace.trans parentTrace).trans returnTrace
  have combinedBelow := TraceBelow.trans _ _
    (TraceBelow.trans _ _ startBelow parentBelow) returnBelow
  have bundled : ∃ fresh : Trace hash image s 1743 1848 15 15
      (Keygen.returnState root), TraceBelow hash fresh := by
    convert (show ∃ fresh : Trace hash image s
      (72+1668+3) (72+1773+3) ((0+15)+0) ((0+15)+0)
      (Keygen.returnState root), TraceBelow hash fresh from
        ⟨combined,combinedBelow⟩) using 1 <;> decide
  obtain ⟨fresh,freshBelow⟩ := bundled
  exact below_of_same trace fresh freshBelow

#print axioms trace_end_unique
#print axioms inner_fold_below
#print axioms first_level_below
#print axioms height_step_below
#print axioms terminal_below
#print axioms all_height3_below
#print axioms all_height4_below
#print axioms start_below
#print axioms return_below
#print axioms callee_height3_below
#print axioms callee_height4_below
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeBelow67
