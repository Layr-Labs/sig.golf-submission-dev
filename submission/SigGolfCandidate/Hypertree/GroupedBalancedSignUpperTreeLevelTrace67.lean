import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreePreludeTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStack67

/-! Control and resource induction across one upper parent-tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLevelTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

structure Ready (heightMax treeBase witnessBase height limit source target : Nat)
    (s : MachineState) : Prop where
  pc : s.pc = 0x1e94
  levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height
  treeWord : s.getMem 0x81000 = BitVec.ofNat 64 (treeBase+height)
  maxLevel : s.getMem 0x81060 = BitVec.ofNat 64 heightMax
  witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase
  selectedBound : (s.getMem 0x810e8).toNat < 1024
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target

theorem transition_pc (s : MachineState)
    (heightMax height : Nat)
    (pc : s.pc = 0x2058)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (maxLevel : s.getMem 0x81060 = BitVec.ofNat 64 heightMax)
    (bound : height < 4)
    (maxBound : heightMax = 3 ∨ heightMax = 4) :
    (step s).pc = if height+1 ≠ heightMax then 0x1e04 else 0x20ec := by
  let swapped := GroupedBalancedSignBottomTreeLevelSwap67.swapState s
  let advanced := GroupedBalancedSignBottomTreeLevelAdvance67.advanceState swapped
  have p1 := GroupedBalancedSignBottomTreeLevelSwap67.swap_pc s pc
  have p2 := GroupedBalancedSignBottomTreeLevelAdvance67.advance_pc swapped p1
  have regs := GroupedBalancedSignBottomTreeLevelAdvance67.advance_regs swapped
    (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)
  have witnessWord : swapped.getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81050
      (by decide) (by decide)]
    exact levelWord
  have maxWord : swapped.getMem 0x81060 = BitVec.ofNat 64 heightMax := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81060
      (by decide) (by decide)]
    exact maxLevel
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState advanced).pc = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_pc advanced p2,
    regs.1,regs.2,witnessWord,maxWord]
  have small : height+1 < 2^64 := by omega
  have maxSmall : heightMax < 2^64 := by rcases maxBound with rfl | rfl <;> decide
  have eq : (BitVec.ofNat 64 height + 1 ≠ BitVec.ofNat 64 heightMax) =
      (height+1 ≠ heightMax) := by
    by_cases h : height+1 = heightMax
    · subst heightMax
      simp [BitVec.ofNat_add]
    · have wordNe : BitVec.ofNat 64 height + 1 ≠
          BitVec.ofNat 64 heightMax := by
        intro wordEq
        have wordEq' : BitVec.ofNat 64 (height+1) =
            BitVec.ofNat 64 heightMax := by
          simpa [BitVec.ofNat_add] using wordEq
        have nat := congrArg BitVec.toNat wordEq'
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
          Nat.mod_eq_of_lt maxSmall] at nat
        exact h nat
      simp only [h, ne_eq, not_false_eq_true]
      exact eq_true wordNe
  simpa only [eq]

theorem transition_controls (s : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (pc : s.pc = 0x2058)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (treeWord : s.getMem 0x81000 = BitVec.ofNat 64 (treeBase+height))
    (maxLevel : s.getMem 0x81060 = BitVec.ofNat 64 heightMax)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (selectedBound : (s.getMem 0x810e8).toNat < 1024)
    (count : s.getMem 0x810d0 = BitVec.ofNat 64 limit)
    (sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source)
    (targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (small : limit ≤ 8)
    (heightBound : height < 4) (treeBound : treeBase+height+1 < 2^64)
    (maxBound : heightMax = 3 ∨ heightMax = 4) :
    (step s).pc = (if height+1 ≠ heightMax then 0x1e04 else 0x20ec) ∧
    (step s).getMem 0x81050 = BitVec.ofNat 64 (height+1) ∧
    (step s).getMem 0x81000 = BitVec.ofNat 64 (treeBase+(height+1)) ∧
    (step s).getMem 0x81060 = BitVec.ofNat 64 heightMax ∧
    (step s).getMem 0x810f8 = BitVec.ofNat 64 witnessBase ∧
    ((step s).getMem 0x810e8).toNat < 1024 ∧
    (step s).getMem 0x810d0 = BitVec.ofNat 64 (limit/2) ∧
    (step s).getMem 0x810c0 = BitVec.ofNat 64 target ∧
    (step s).getMem 0x810c8 = BitVec.ofNat 64 source := by
  have frame (a : Word) (h0 : a ≠ 0x810c0) (h1 : a ≠ 0x810c8)
      (h2 : a ≠ 0x810d0) (h3 : a ≠ 0x81000) (h4 : a ≠ 0x81050) :
      (step s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeLevelData67.frame s a h0 h1 h2 h3 h4
  refine ⟨transition_pc s heightMax height pc levelWord maxLevel heightBound
    maxBound,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [GroupedBalancedSignBottomTreeLevelData67.witness_level,levelWord]
    simp [BitVec.ofNat_add]
  · rw [GroupedBalancedSignBottomTreeLevelData67.height,treeWord]
    simp [BitVec.ofNat_add,BitVec.add_assoc,Nat.add_assoc]
  · rw [frame 0x81060 (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact maxLevel
  · rw [frame 0x810f8 (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact witness
  · rw [frame 0x810e8 (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact selectedBound
  · rw [GroupedBalancedSignBottomTreeLevelData67.count,count]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  · rw [GroupedBalancedSignBottomTreeLevelData67.source,targetPtr]
  · rw [GroupedBalancedSignBottomTreeLevelData67.target,sourcePtr]

theorem height_step (hash : Hash) (s : MachineState)
    (heightMax treeBase witnessBase height limit source target : Nat)
    (ready : Ready heightMax treeBase witnessBase height limit source target s)
    (heightBound : height+1 < heightMax)
    (maxBound : heightMax = 3 ∨ heightMax = 4)
    (treeBound : treeBase+heightMax < 2^64)
    (witnessBound : witnessBase+16*heightMax+16 ≤ 0x80000)
    (witnessAligned : witnessBase % 8 = 0)
    (positive : 0 < limit) (small : limit ≤ 8)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000)) :
    ∃ next : MachineState,
      Trace hash image s
        (113+84*(limit-1)+85) (120+91*(limit-1)+85)
        limit limit next ∧
      Ready heightMax treeBase witnessBase (height+1) (limit/2)
        target source next ∧
      next.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, 0x90000 ≤ a.toNat →
        next.getMem a = s.getMem a) := by
  have hb : height < 10 := by
    rcases maxBound with rfl | rfl <;> omega
  have hwb : witnessBase+16*height+16 ≤ 0x80000 := by
    omega
  obtain ⟨done,parentTrace,doneInv,parentFrame,parentSp,parentHigh⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.first_level hash s height
      witnessBase limit source target ready.pc ready.levelWord ready.witness
      hb hwb witnessAligned ready.selectedBound ready.count ready.sourcePtr
      ready.targetPtr bases positive small
  have stable (a : Word) (ha : 0x81000 ≤ a.toNat)
      (hb : a.toNat < 0x83000) (h08 : a ≠ 0x81008)
      (hd8 : a ≠ 0x810d8) : done.getMem a = s.getMem a :=
    parentFrame a ⟨ha,hb,h08,hd8⟩
  have levelWord : done.getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [stable 0x81050 (by decide) (by decide) (by decide) (by decide)]
    exact ready.levelWord
  have treeWord : done.getMem 0x81000 =
      BitVec.ofNat 64 (treeBase+height) := by
    rw [stable 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact ready.treeWord
  have maxLevel : done.getMem 0x81060 = BitVec.ofNat 64 heightMax := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide)]
    exact ready.maxLevel
  have witness : done.getMem 0x810f8 = BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.witness
  have selectedBound : (done.getMem 0x810e8).toNat < 1024 := by
    rw [stable 0x810e8 (by decide) (by decide) (by decide) (by decide)]
    exact ready.selectedBound
  have transitionTrace : Trace hash image done 37 37 0 0 (step done) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps done
      doneInv.pc).trace
  obtain ⟨transitionPc,levelNext,treeNext,maxNext,witnessNext,
    selectedNext,countNext,sourceNext,targetNext⟩ :=
    transition_controls done heightMax treeBase witnessBase height limit source
      target doneInv.pc levelWord treeWord maxLevel witness selectedBound
      doneInv.count doneInv.sourcePtr doneInv.targetPtr small
      (by omega) (by omega) maxBound
  have nextPc : (step done).pc = 0x1e04 := by
    rw [transitionPc]
    simp [Nat.ne_of_lt heightBound]
  obtain ⟨next,prelude,preludePc,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude (step done) nextPc
  have fromStep (a : Word)
      (h0 : a ≠ 0x81008) (h1 : a ≠ 0x81010) (h2 : a ≠ 0x81018)
      (h3 : a ≠ 0x810a8) (h4 : a ≠ 0x810b0) (h5 : a ≠ 0x810b8) :
      next.getMem a = (step done).getMem a :=
    preludeFrame a h0 h1 h2 h3 h4 h5
  refine ⟨next,?_,?_,?_,?_⟩
  · have combined := (parentTrace.trans transitionTrace).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> omega
  · refine ⟨preludePc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [fromStep 0x81050 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact levelNext
    · rw [fromStep 0x81000 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact treeNext
    · rw [fromStep 0x81060 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact maxNext
    · rw [fromStep 0x810f8 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact witnessNext
    · rw [fromStep 0x810e8 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact selectedNext
    · rw [fromStep 0x810d0 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact countNext
    · rw [fromStep 0x810c0 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact sourceNext
    · rw [fromStep 0x810c8 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; exact targetNext
  · exact (GroupedBalancedSignBottomTreeLevelStack67.prelude_sp
      (step done) next nextPc prelude).trans
      ((GroupedBalancedSignBottomTreeLevelStack67.transition_sp done).trans
        parentSp)
  · intro a high
    have transitionFrame : (step done).getMem a = done.getMem a :=
      GroupedBalancedSignBottomTreeLevelData67.frame done a
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
        (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
    exact (fromStep a
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)
      (by intro eq; have hn := congrArg BitVec.toNat eq; simp at hn; omega)).trans
      (transitionFrame.trans (parentHigh a high))

#print axioms transition_pc
#print axioms transition_controls
#print axioms height_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeLevelTrace67
