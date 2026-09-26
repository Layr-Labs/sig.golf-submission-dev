import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeTerminalData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStart67
import SigGolfCandidate.TraceDeterminism

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStartData67. -/
section
/-! Functional root and exact resource trace for an upper h3/h4 Merkle tree. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
open GroupedBalancedSignUpperTreeFirstLevelData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

theorem height3 (hash : Hash) (treeBase leafBase witnessBase addressBase : Nat)
    (leaves : Nat → Reference.Digest) (s : MachineState)
    (params : Params leafBase 0 4 0x83000 0x88000 addressBase)
    (start : Start hash treeBase leafBase leaves 3 witnessBase 0 4
      0x83000 0x88000 addressBase s)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final : MachineState,
      Trace hash image s 882 931 7 7 final ∧
      final.pc=0x20ec ∧ final.getMem 0x810c0=0x88000 ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x88000+8*i.val))=
          (node hash treeBase leafBase leaves 3 0).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨s1,t0,p1,start1⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 3 witnessBase 0 4 0x83000 0x88000 addressBase s
      params start (by decide) (Or.inl rfl) treeBound witnessBound
      witnessAligned (by decide) (by decide) (Or.inr (Or.inl rfl))
  obtain ⟨s2,t1,p2,start2⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 3 witnessBase 1 2 0x88000 0x83000 (addressBase/2)
      s1 (by simpa only [show 4/2=2 by decide] using p1)
      (by simpa only [show 4/2=2 by decide] using start1)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inl rfl)
  obtain ⟨final,t2,pc,ptr,root⟩ :=
    GroupedBalancedSignUpperTreeTerminalData67.terminal_root hash treeBase
      leafBase leaves 3 witnessBase 2 0x83000 0x88000
      ((addressBase/2)/2) s2
      (by simpa only [show 2/2=1 by decide] using p2)
      (by simpa only [show 2/2=1 by decide] using start2)
      (by decide) (Or.inl rfl) treeBound witnessBound witnessAligned
  refine ⟨final,?_,pc,ptr,root⟩
  have combined := (t0.trans t1).trans t2
  convert combined using 1 <;> decide

theorem height4 (hash : Hash) (treeBase leafBase witnessBase addressBase : Nat)
    (leaves : Nat → Reference.Digest) (s : MachineState)
    (params : Params leafBase 0 8 0x83000 0x88000 addressBase)
    (start : Start hash treeBase leafBase leaves 4 witnessBase 0 8
      0x83000 0x88000 addressBase s)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final : MachineState,
      Trace hash image s 1668 1773 15 15 final ∧
      final.pc=0x20ec ∧ final.getMem 0x810c0=0x83000 ∧
      (∀ i : Fin 2,
        final.getMem (BitVec.ofNat 64 (0x83000+8*i.val))=
          (node hash treeBase leafBase leaves 4 0).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨s1,t0,p1,start1⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 0 8 0x83000 0x88000 addressBase s
      params start (by decide) (Or.inr rfl) treeBound witnessBound
      witnessAligned (by decide) (by decide) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨s2,t1,p2,start2⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 1 4 0x88000 0x83000 (addressBase/2)
      s1 (by simpa only [show 8/2=4 by decide] using p1)
      (by simpa only [show 8/2=4 by decide] using start1)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inr (Or.inl rfl))
  obtain ⟨s3,t2,p3,start3⟩ :=
    GroupedBalancedSignUpperTreeStepData67.height_step_data hash treeBase
      leafBase leaves 4 witnessBase 2 2 0x83000 0x88000
      ((addressBase/2)/2) s2
      (by simpa only [show 4/2=2 by decide] using p2)
      (by simpa only [show 4/2=2 by decide] using start2)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
      (by decide) (by decide) (Or.inl rfl)
  obtain ⟨final,t3,pc,ptr,root⟩ :=
    GroupedBalancedSignUpperTreeTerminalData67.terminal_root hash treeBase
      leafBase leaves 4 witnessBase 3 0x88000 0x83000
      (((addressBase/2)/2)/2) s3
      (by simpa only [show 2/2=1 by decide] using p3)
      (by simpa only [show 2/2=1 by decide] using start3)
      (by decide) (Or.inr rfl) treeBound witnessBound witnessAligned
  refine ⟨final,?_,pc,ptr,root⟩
  have combined := ((t0.trans t1).trans t2).trans t3
  convert combined using 1 <;> decide

#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeAllData67

end

/-! The upper leaf table and rounded index enter the shared Merkle callee. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStartData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeFirstLevelData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem start_data (hash : Hash) (treeBase leafBase witnessBase limit height : Nat)
    (leaves : Nat → Reference.Digest) (s : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff7e0 ∨ s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=BitVec.ofNat 64 height)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=BitVec.ofNat 64 (2*limit))
    (limitBound : limit≤8)
    (leafBound : leafBase<2^192)
    (scratch : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*i.val) 64)
    (leavesReady : ∀ j, j<2*limit → ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (leaves j).extractLsb' (64*i.val) 64) :
    ∃ ready : MachineState,
      Trace hash image s 72 72 0 0 ready ∧
      Start hash treeBase leafBase leaves height witnessBase 0 limit
        0x83000 0x88000 (leafBase/2) ready ∧
      ready.getReg .x2=s.getReg .x2-16 ∧
      ready.getMem (s.getReg .x2-16)=0x1c34 := by
  obtain ⟨ready,run,readyInv,readySp,readyLink⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s height treeBase
      witnessBase limit pc sp tree maxLevel witness selected count
      (by omega)
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
  have slotHigh : 0x90000≤(s.getReg .x2-16).toNat := by
    rcases sp with h|h <;> rw [h] <;> decide
  have initialScratch : ∀ i : Fin 3,
      initialized.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomTreeInitData67.init_frame entered _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    have low : (Signing.wordAddress 0x810a8 i.val).toNat<0x90000 := by
      fin_cases i <;> decide
    have neSlot : Signing.wordAddress 0x810a8 i.val≠called.getReg .x2-16 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [GroupedBalancedSignUpperTreeCall67.call_sp] at hn
      omega
    rw [GroupedBalancedSignBottomTreeEntryData67.entry_frame called _ neSlot
      (by fin_cases i <;> decide),
      GroupedBalancedSignUpperTreeCall67.call_mem]
    exact scratch i
  obtain ⟨built,prelude,_,addressWords,scratchWords,preludeFrame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude initialized
      (BitVec.ofNat 192 leafBase) initPc initialScratch
  have builtTrace : Trace hash image s 72 72 0 0 built := by
    have combined := (((OrdinarySteps.trace (hash := hash) callSteps).trans
      (OrdinarySteps.trace (hash := hash) entrySteps)).trans
      (OrdinarySteps.trace (hash := hash) initSteps)).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> decide
  have same := Trace.deterministic run builtTrace
  have shifted : (BitVec.ofNat 192 leafBase >>> 1)=
      BitVec.ofNat 192 (leafBase/2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have sourceWords : ∀ j, j<2*limit → ∀ i : Fin 2,
      ready.getMem (BitVec.ofNat 64 (0x83000+16*j+8*i.val))=
        (leaves j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    let a : Word := BitVec.ofNat 64 (0x83000+16*j+8*i.val)
    have nat : a.toNat=0x83000+16*j+8*i.val := by
      simp only [a,BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have high : 0x83000≤a.toNat ∧ a.toNat<0x90000 := by
      rw [nat]
      omega
    have neLow (b : Word) (lo : b.toNat<0x83000) : a≠b := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nat] at hn
      omega
    have neStack : a≠called.getReg .x2-16 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nat,GroupedBalancedSignUpperTreeCall67.call_sp] at hn
      omega
    rw [same,preludeFrame a
      (neLow 0x81008 (by decide)) (neLow 0x81010 (by decide))
      (neLow 0x81018 (by decide)) (neLow 0x810a8 (by decide))
      (neLow 0x810b0 (by decide)) (neLow 0x810b8 (by decide)),
      GroupedBalancedSignBottomTreeInitData67.init_frame entered a
        (neLow 0x810c0 (by decide)) (neLow 0x810c8 (by decide))
        (neLow 0x810d0 (by decide)),
      GroupedBalancedSignBottomTreeEntryData67.entry_frame called a
        neStack (neLow 0x81050 (by decide)),
      GroupedBalancedSignUpperTreeCall67.call_mem]
    exact leavesReady j hj i
  have address : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x81008 i.val)=
        (BitVec.ofNat 192 (leafBase/2)).extractLsb'
          (64*i.val) 64 := by
    intro i
    rw [same,addressWords i,shifted]
  have scratchReady : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 (leafBase/2)).extractLsb'
          (64*i.val) 64 := by
    intro i
    rw [same,scratchWords i,shifted]
  exact ⟨ready,run,⟨readyInv,address,sourceWords,scratchReady⟩,
    readySp,readyLink⟩

#print axioms start_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeStartData67
