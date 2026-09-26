import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickReady67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickControl67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private def selected (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectPtr67.selectState s
private def copied (s : MachineState) :=
  GroupedBalancedSignBottomTreeSelectCopy67.copyState (selected s)
private def paired (s : MachineState) :=
  GroupedBalancedSignBottomTreePairPtr67.pairState (copied s)
private def loaded (s : MachineState) :=
  GroupedBalancedSignBottomTreePairLoad67.loadState (paired s)
private def children (s : MachineState) :=
  GroupedBalancedSignBottomTreeNodeInput67.inputState (loaded s)
theorem hashed_pc (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1e94) :
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s).pc = 0x1fd8 := by
  have p1 := GroupedBalancedSignBottomTreeSelectPtr67.select_pc s pc
  have p2 := GroupedBalancedSignBottomTreeSelectCopy67.copy_pc (selected s) p1
  have p3 := GroupedBalancedSignBottomTreePairPtr67.pair_pc (copied s) p2
  have p4 := GroupedBalancedSignBottomTreePairLoad67.load_pc (paired s) p3
  have p5 := GroupedBalancedSignBottomTreeNodeInput67.input_pc (loaded s) p4
  have p6 := GroupedBalancedSignBottomTreeH4Prelude67.prelude_pc (children s) p5
  rw [GroupedBalancedSignBottomTreeFirstTickData67.hashed,Keygen.hash_pc]
  change (GroupedBalancedSignBottomTreeH4Prelude67.preludeState (children s)).pc + 4 = _
  rw [p6]
  decide
theorem stored_pc (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1e94) :
    (GroupedBalancedSignBottomTreeFirstTickData67.stored hash s).pc = 0x2010 := by
  have p6 := hashed_pc hash s pc
  have p7 := GroupedBalancedSignBottomTreeHashStorePtr67.store_pc
    (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s) p6
  exact GroupedBalancedSignBottomTreeHashStoreCopy67.copy_pc
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState (GroupedBalancedSignBottomTreeFirstTickData67.hashed hash s)) p7
theorem advanced_pc (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1e94) :
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).pc = 0x2054 := by
  exact GroupedBalancedSignBottomTreeParentAdvance67.advance_pc
    (GroupedBalancedSignBottomTreeFirstTickData67.stored hash s) (stored_pc hash s pc)
theorem tick_pc (hash : Hash) (s : MachineState)
    (level target : Nat)
    (pc : s.pc = 0x1e94)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (GroupedBalancedSignBottomTreeFirstTickData67.tickState hash s).pc =
      if (1 : Word) ≠ s.getMem 0x810d0 then 0x1f08 else 0x2058 := by
  have regs := GroupedBalancedSignBottomTreeParentControl67.advance_regs
    (GroupedBalancedSignBottomTreeFirstTickData67.stored hash s)
  have r6 : (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).getReg .x6 = 1 := by
    rw [GroupedBalancedSignBottomTreeFirstTickData67.advanced,regs.1,
      GroupedBalancedSignBottomTreeFirstTickData67.stored_from_hashed hash s level target 0x810d8 levelWord
        witnessBase levelBound destination targetCase (by decide),
      GroupedBalancedSignBottomTreeFirstTickData67.hashed_counter]
    decide
  have r7 : (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s).getReg .x7 = s.getMem 0x810d0 := by
    rw [GroupedBalancedSignBottomTreeFirstTickData67.advanced,regs.2,
      GroupedBalancedSignBottomTreeFirstTickData67.stored_control_frame hash s level target 0x810d0 levelWord
        witnessBase levelBound destination targetCase (by decide) (by decide)
        (by decide)]
  exact (GroupedBalancedSignBottomTreeParentControl67.branch_pc
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s) (advanced_pc hash s pc)).trans (by rw [r6,r7])
#print axioms hashed_pc
#print axioms stored_pc
#print axioms advanced_pc
#print axioms tick_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickControl67
