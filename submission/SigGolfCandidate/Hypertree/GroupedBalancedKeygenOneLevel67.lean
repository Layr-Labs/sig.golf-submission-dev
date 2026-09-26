import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodesFold67

/-! Keygen tree setup values. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenSetupControls67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
private abbrev setupState := GroupedBalancedKeygenTreeSetup67.setupState

theorem setup_pc (s : MachineState) (pc : s.pc = 0x1428) :
    (setupState s).pc = 0x1480 := by
  simp [setupState,GroupedBalancedKeygenTreeSetup67.setupState,execInstrBr,pc]

theorem setup_controls (s : MachineState) :
    (setupState s).getMem 0x81070#64 = 8 ∧
    (setupState s).getMem 0x81078#64 = 0x82000 ∧
    (setupState s).getMem 0x81080#64 = 0x82100 ∧
    (setupState s).getMem 0x81050#64 = 0 ∧
    (setupState s).getMem 0x81040#64 = 0 ∧
    (setupState s).getMem 0x81000#64 = s.getMem 0x81000#64 := by
  simp [setupState,GroupedBalancedKeygenTreeSetup67.setupState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms setup_controls
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenSetupControls67

/-! A complete H4 parent-tree level, including buffer swap and counter halving. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedKeygenImage67.image

theorem one_level (hash : Hash) (s : MachineState) (k src dst ell : Nat)
    (pc : s.pc = 0x1480) (positive : 0 < k) (bound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = 0)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (treeLevel : s.getMem 0x81050#64 = BitVec.ofNat 64 ell) :
    ∃ final,
      Trace hash image s (79*k+35) (86*k+35) k k final ∧
      final.pc = (if BitVec.ofNat 64 ell + 1 = 4 then 0x1648 else 0x1470) ∧
      final.getMem 0x81070#64 = BitVec.ofNat 64 k >>> 1 ∧
      final.getMem 0x81078#64 = BitVec.ofNat 64 dst ∧
      final.getMem 0x81080#64 = BitVec.ofNat 64 src ∧
      final.getMem 0x81050#64 = BitVec.ofNat 64 ell + 1 ∧
      final.getMem 0x81000#64 = s.getMem 0x81000#64 + 1 := by
  obtain ⟨nodes,first,nodesPC,_,nodesFrame⟩ :=
    GroupedBalancedKeygenNodesFold67.nodes hash s 0 k src dst pc positive
      (by omega) srcCase dstCase (by simpa using index)
      (by simpa using count) source destination
  let final := GroupedBalancedKeygenLevel67.levelState nodes
  have second : Trace hash image nodes 35 35 0 0 final :=
    (GroupedBalancedKeygenLevel67.level_steps nodes nodesPC).trace
  obtain ⟨srcNext,dstNext,countNext,levelNext,treeNext,_⟩ :=
    GroupedBalancedKeygenLevel67.level_controls nodes
  have nframe (a : Word) (high : 0x81000 ≤ a.toNat)
      (low : a.toNat < 0x82000) (ne08 : a ≠ 0x81008#64)
      (ne40 : a ≠ 0x81040#64) : nodes.getMem a = s.getMem a :=
    nodesFrame a high low ne08 ne40
  refine ⟨final,by simpa only [Nat.add_assoc,Nat.add_zero] using first.trans second,?_,?_,?_,?_,?_,?_⟩
  · rw [GroupedBalancedKeygenLevel67.level_pc nodes nodesPC,
      nframe 0x81050#64 (by decide) (by decide) (by decide) (by decide),treeLevel]
  · rw [countNext,nframe 0x81070#64 (by decide) (by decide) (by decide) (by decide),count]
  · rw [srcNext,nframe 0x81080#64 (by decide) (by decide) (by decide) (by decide),destination]
  · rw [dstNext,nframe 0x81078#64 (by decide) (by decide) (by decide) (by decide),source]
  · rw [treeNext,nframe 0x81050#64 (by decide) (by decide) (by decide) (by decide),treeLevel]
  · rw [levelNext,nframe 0x81000#64 (by decide) (by decide) (by decide) (by decide)]

#print axioms one_level
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLevel67
