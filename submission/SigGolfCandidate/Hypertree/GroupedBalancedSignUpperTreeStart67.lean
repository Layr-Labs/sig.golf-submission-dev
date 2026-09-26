import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInitData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreePreludeTrace67


/-! Concrete call into the shared parent-tree builder from an upper leaf group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCall67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

def called (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x1 0x178)

theorem call_step (s : MachineState) (pc : s.pc=0x1c30) :
    OrdinarySteps image s 1 (called s) := by
  have code : Keygen.instructionAt image 0x1c30 =
      some (.base (.JAL .x1 0x178)) := by decide
  apply OrdinarySteps.step s (called s) _ (.base (.JAL .x1 0x178)) 0
  · simpa only [Keygen.fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _

theorem call_pc (s : MachineState) (pc : s.pc=0x1c30) :
    (called s).pc=0x1da8 := by
  simp [called,execInstrBr,pc,signExtend21]

theorem call_link (s : MachineState) (pc : s.pc=0x1c30) :
    (called s).getReg .x1=0x1c34 := by
  simp [called,execInstrBr,pc,MachineState.getReg_setReg_eq]

theorem call_sp (s : MachineState) :
    (called s).getReg .x2=s.getReg .x2 := by
  simp [called,execInstrBr,MachineState.getReg_setReg_ne]

theorem call_mem (s : MachineState) (a : Word) :
    (called s).getMem a=s.getMem a := by
  simp [called,execInstrBr,MachineState.getMem_setReg,
    MachineState.getMem_setPC]

#print axioms call_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCall67


/-! Resource trace and controls at the first upper parent hash. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeLevelTrace67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem start (hash : Hash) (s : MachineState)
    (height treeBase witnessBase limit : Nat)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=BitVec.ofNat 64 height)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=BitVec.ofNat 64 (2*limit))
    (limitBound : limit < 2^63) :
    ∃ ready : MachineState,
      Trace hash image s 72 72 0 0 ready ∧
      Ready height treeBase witnessBase 0 limit 0x83000 0x88000 ready ∧
      ready.getReg .x2=s.getReg .x2-16 ∧
      ready.getMem (s.getReg .x2-16)=0x1c34 := by
  let called := GroupedBalancedSignUpperTreeCall67.called s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let initialized := GroupedBalancedSignBottomTreeInit67.initState entered
  have callSteps := GroupedBalancedSignUpperTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignUpperTreeCall67.call_pc s pc
  have callSp : called.getReg .x2=0xfff7e0 ∨ called.getReg .x2=0xfff700 := by
    rw [GroupedBalancedSignUpperTreeCall67.call_sp]
    exact sp
  have entrySteps := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc callSp
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initSteps := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  obtain ⟨ready,prelude,readyPc,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude initialized initPc
  have run : Trace hash image s 72 72 0 0 ready := by
    have combined := (((OrdinarySteps.trace (hash := hash) callSteps).trans
      (OrdinarySteps.trace (hash := hash) entrySteps)).trans
      (OrdinarySteps.trace (hash := hash) initSteps)).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> decide
  have slotHigh : 0x90000 ≤ (s.getReg .x2-16).toNat := by
    rcases sp with h | h <;> rw [h] <;> decide
  have preludeFrame' (a : Word)
      (safe : a ≠ 0x81008 ∧ a ≠ 0x81010 ∧ a ≠ 0x81018 ∧
        a ≠ 0x810a8 ∧ a ≠ 0x810b0 ∧ a ≠ 0x810b8) :
      ready.getMem a=initialized.getMem a := by
    exact preludeFrame a safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1
      safe.2.2.2.2.1 safe.2.2.2.2.2
  have initFrame (a : Word) (notC0 : a≠0x810c0)
      (notC8 : a≠0x810c8) (notD0 : a≠0x810d0) :
      initialized.getMem a=entered.getMem a :=
    GroupedBalancedSignBottomTreeInitData67.init_frame entered a
      notC0 notC8 notD0
  have entryFrame (a : Word) (low : a.toNat<0x90000)
      (not50 : a≠0x81050) : entered.getMem a=s.getMem a := by
    have slotNe : a≠called.getReg .x2-16 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [GroupedBalancedSignUpperTreeCall67.call_sp] at hn
      omega
    exact (GroupedBalancedSignBottomTreeEntryData67.entry_frame called a
      slotNe not50).trans (GroupedBalancedSignUpperTreeCall67.call_mem s a)
  have stable (a : Word) (low : a.toNat<0x90000)
      (preSafe : a ≠ 0x81008 ∧ a ≠ 0x81010 ∧ a ≠ 0x81018 ∧
        a ≠ 0x810a8 ∧ a ≠ 0x810b0 ∧ a ≠ 0x810b8)
      (not50 : a≠0x81050) (notC0 : a≠0x810c0)
      (notC8 : a≠0x810c8) (notD0 : a≠0x810d0) :
      ready.getMem a=s.getMem a :=
    (preludeFrame' a preSafe).trans
      ((initFrame a notC0 notC8 notD0).trans (entryFrame a low not50))
  have readyTree : ready.getMem 0x81000=BitVec.ofNat 64 treeBase := by
    rw [stable 0x81000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact tree
  have readyMax : ready.getMem 0x81060=BitVec.ofNat 64 height := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact maxLevel
  have readyWitness : ready.getMem 0x810f8=BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact witness
  have readySelected : (ready.getMem 0x810e8).toNat<1024 := by
    rw [stable 0x810e8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact selected
  have readyLevel : ready.getMem 0x81050=0 := by
    rw [preludeFrame' 0x81050 (by decide),
      initFrame 0x81050 (by decide) (by decide) (by decide)]
    exact GroupedBalancedSignBottomTreeEntry67.entry_level called
  have readySource : ready.getMem 0x810c0=0x83000 := by
    rw [preludeFrame' 0x810c0 (by decide)]
    exact GroupedBalancedSignBottomTreeInitData67.init_source entered
  have readyTarget : ready.getMem 0x810c8=0x88000 := by
    rw [preludeFrame' 0x810c8 (by decide)]
    exact GroupedBalancedSignBottomTreeInitData67.init_target entered
  have readyCount : ready.getMem 0x810d0=BitVec.ofNat 64 limit := by
    rw [preludeFrame' 0x810d0 (by decide),
      GroupedBalancedSignBottomTreeInitData67.init_count,
      entryFrame 0x810d0 (by decide) (by decide),count]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have readyInv : Ready height treeBase witnessBase 0 limit 0x83000 0x88000 ready :=
    ⟨readyPc,readyLevel,by simpa using readyTree,readyMax,
      readyWitness,readySelected,readyCount,readySource,readyTarget⟩
  have readySp : ready.getReg .x2=s.getReg .x2-16 := by
    exact (GroupedBalancedSignBottomTreeLevelStack67.prelude_sp
      initialized ready initPc prelude).trans
      ((GroupedBalancedSignBottomTreeInitData67.init_stack entered).trans
        ((GroupedBalancedSignBottomTreeEntryData67.entry_stack called).trans
          (by rw [GroupedBalancedSignUpperTreeCall67.call_sp])))
  have slotWord : ready.getMem (s.getReg .x2-16)=0x1c34 := by
    have highNe (a : Word) (low : a.toNat < 0x90000) :
        s.getReg .x2-16 ≠ a := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      omega
    have separate : called.getReg .x2-16 ≠ 0x81050 := by
      rcases callSp with h|h <;> rw [h] <;> decide
    have entrySlot := GroupedBalancedSignBottomTreeEntryData67.entry_saved_link
      called separate
    rw [GroupedBalancedSignUpperTreeCall67.call_sp] at entrySlot
    have preludeSlot := preludeFrame (s.getReg .x2-16)
      (highNe 0x81008 (by decide)) (highNe 0x81010 (by decide))
      (highNe 0x81018 (by decide)) (highNe 0x810a8 (by decide))
      (highNe 0x810b0 (by decide)) (highNe 0x810b8 (by decide))
    rw [preludeSlot,
      initFrame (s.getReg .x2-16)
        (highNe 0x810c0 (by decide)) (highNe 0x810c8 (by decide))
        (highNe 0x810d0 (by decide))]
    exact entrySlot.trans (GroupedBalancedSignUpperTreeCall67.call_link s pc)
  exact ⟨ready,run,readyInv,readySp,slotWord⟩

#print axioms start
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStart67
