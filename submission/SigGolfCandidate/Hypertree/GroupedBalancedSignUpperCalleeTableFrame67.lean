import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeByteCallee67

/-! ByteSign Merkle callee preserves the decoder table above the caller stack. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTableFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev oldImage := GroupedBalancedSignImage67.image

theorem start_table (hash : Hash) (s ready : MachineState)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff700)
    (trace : Trace hash oldImage s 72 72 0 0 ready)
    (a : Word) (table : 0xfff700≤a.toNat) :
    ready.getMem a=s.getMem a := by
  let called := GroupedBalancedSignUpperTreeCall67.called s
  let entered := GroupedBalancedSignBottomTreeEntry67.entryState called
  let initialized := GroupedBalancedSignBottomTreeInit67.initState entered
  have callSteps := GroupedBalancedSignUpperTreeCall67.call_step s pc
  have callPc := GroupedBalancedSignUpperTreeCall67.call_pc s pc
  have callSp : called.getReg .x2=0xfff700 := by
    rw [GroupedBalancedSignUpperTreeCall67.call_sp]
    exact sp
  have entrySteps := GroupedBalancedSignBottomTreeEntryStack67.entry_steps_stack
    called callPc (Or.inr callSp)
  have entryPc := GroupedBalancedSignBottomTreeEntry67.entry_pc called callPc
  have initSteps := GroupedBalancedSignBottomTreeInit67.init_steps entered entryPc
  have initPc := GroupedBalancedSignBottomTreeInit67.init_pc entered entryPc
  obtain ⟨built,prelude,_,preludeFrame⟩ :=
    GroupedBalancedSignUpperTreePreludeTrace67.prelude initialized initPc
  have builtTrace : Trace hash oldImage s 72 72 0 0 built := by
    have combined := (((OrdinarySteps.trace (hash := hash) callSteps).trans
      (OrdinarySteps.trace (hash := hash) entrySteps)).trans
      (OrdinarySteps.trace (hash := hash) initSteps)).trans
      (OrdinarySteps.trace (hash := hash) prelude)
    convert combined using 1 <;> decide
  have same := Trace.deterministic trace builtTrace
  have ne (b : Word) (hb : b.toNat<0x90000) : a≠b := by
    intro eq
    subst a
    omega
  have neSlot : a≠called.getReg .x2-16 := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    rw [callSp] at hn
    have slot : ((0xfff700 : Word)-16).toNat=0xfff6f0 := by decide
    rw [slot] at hn
    omega
  rw [same,
    preludeFrame a
      (ne 0x81008 (by decide)) (ne 0x81010 (by decide))
      (ne 0x81018 (by decide)) (ne 0x810a8 (by decide))
      (ne 0x810b0 (by decide)) (ne 0x810b8 (by decide)),
    GroupedBalancedSignBottomTreeInitData67.init_frame entered a
      (ne 0x810c0 (by decide)) (ne 0x810c8 (by decide))
      (ne 0x810d0 (by decide)),
    GroupedBalancedSignBottomTreeEntryData67.entry_frame called a neSlot
      (ne 0x81050 (by decide)),
    GroupedBalancedSignUpperTreeCall67.call_mem]

theorem height3 (hash : Hash) (s returned : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 957 1006 7 7 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=3)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=8)
    (treeBound : treeBase+3<2^64)
    (witnessBound : witnessBase+16*3+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (a : Word) (table : 0xfff700≤a.toNat) :
    returned.getMem a=s.getMem a := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 3 treeBase witnessBase 4
      pc (Or.inr sp) tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height3 hash ready treeBase
      witnessBase startInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final
      (Or.inr sp) slot readySp finalSp finalHigh finalPc
  have oldTrace : Trace hash oldImage s 957 1006 7 7
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have built : Trace hash image s 957 1006 7 7
      (Keygen.returnState final) :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height3 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc (Or.inr sp)
      tree maxLevel witness selected count treeBound witnessBound witnessAligned
  have same := Trace.deterministic trace built
  rw [same,Keygen.return_mem]
  exact (finalHigh a (by omega)).trans
    (start_table hash s ready pc sp startTrace a table)

theorem height4 (hash : Hash) (s returned : MachineState)
    (treeBase witnessBase : Nat)
    (trace : Trace hash image s 1743 1848 15 15 returned)
    (pc : s.pc=0x1c30)
    (sp : s.getReg .x2=0xfff700)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (maxLevel : s.getMem 0x81060=4)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (selected : (s.getMem 0x810e8).toNat<1024)
    (count : s.getMem 0x810d0=16)
    (treeBound : treeBase+4<2^64)
    (witnessBound : witnessBase+16*4+16≤0x80000)
    (witnessAligned : witnessBase%8=0)
    (a : Word) (table : 0xfff700≤a.toNat) :
    returned.getMem a=s.getMem a := by
  obtain ⟨ready,startTrace,startInv,readySp,slot⟩ :=
    GroupedBalancedSignUpperTreeStart67.start hash s 4 treeBase witnessBase 8
      pc (Or.inr sp) tree maxLevel witness selected count (by decide)
  obtain ⟨final,parentTrace,finalPc,_,finalSp,finalHigh⟩ :=
    GroupedBalancedSignUpperTreeAllTrace67.height4 hash ready treeBase
      witnessBase startInv treeBound witnessBound witnessAligned
  obtain ⟨returnTrace,_,_⟩ :=
    GroupedBalancedSignUpperTreeCallee67.return_after hash s ready final
      (Or.inr sp) slot readySp finalSp finalHigh finalPc
  have oldTrace : Trace hash oldImage s 1743 1848 15 15
      (Keygen.returnState final) := by
    have combined := (startTrace.trans parentTrace).trans returnTrace
    convert combined using 1 <;> decide
  have built : Trace hash image s 1743 1848 15 15
      (Keygen.returnState final) :=
    GroupedBalancedSignUpperTreeByteCallee67.transfer_height4 hash s
      (Keygen.returnState final) treeBase witnessBase oldTrace pc (Or.inr sp)
      tree maxLevel witness selected count treeBound witnessBound witnessAligned
  have same := Trace.deterministic trace built
  rw [same,Keygen.return_mem]
  exact (finalHigh a (by omega)).trans
    (start_table hash s ready pc sp startTrace a table)

#print axioms start_table
#print axioms height3
#print axioms height4
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCalleeTableFrame67
