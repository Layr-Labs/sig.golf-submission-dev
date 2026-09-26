import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairLoad67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentTrace67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
theorem parent_query_trace (hash : Hash)
    (s t1 t2 t3 t4 t5 : MachineState)
    (pc : s.pc = 0x1e94)
    (h1 : t1 = GroupedBalancedSignBottomTreeSelectPtr67.selectState s)
    (h2 : t2 = GroupedBalancedSignBottomTreeSelectCopy67.copyState t1)
    (h3 : t3 = GroupedBalancedSignBottomTreePairPtr67.pairState t2)
    (h4 : t4 = GroupedBalancedSignBottomTreePairLoad67.loadState t3)
    (h5 : t5 = GroupedBalancedSignBottomTreeNodeInput67.inputState t4)
    (src0 : accessValid (t1.getReg .x6) 8 = true)
    (src1 : accessValid (t1.getReg .x6 + 8) 8 = true)
    (dst0 : accessValid (t1.getReg .x7) 8 = true)
    (dst1 : accessValid (t1.getReg .x7 + 8) 8 = true)
    (child0 : accessValid (t3.getReg .x7) 8 = true)
    (child1 : accessValid (t3.getReg .x7 + 8) 8 = true)
    (child2 : accessValid (t3.getReg .x7 + 16) 8 = true)
    (child3 : accessValid (t3.getReg .x7 + 24) 8 = true) :
    Trace hash image s 81 88 1 1
      (writeHash (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5)
        (hash (hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5)))) := by
  have p1 : t1.pc = 0x1ee8 := by
    rw [h1]
    exact GroupedBalancedSignBottomTreeSelectPtr67.select_pc s pc
  have p2 : t2.pc = 0x1ef8 := by
    rw [h2]
    exact GroupedBalancedSignBottomTreeSelectCopy67.copy_pc t1 p1
  have p3 : t3.pc = 0x1f28 := by
    rw [h3]
    exact GroupedBalancedSignBottomTreePairPtr67.pair_pc t2 p2
  have p4 : t4.pc = 0x1f38 := by
    rw [h4]
    exact GroupedBalancedSignBottomTreePairLoad67.load_pc t3 p3
  have p5 : t5.pc = 0x1f50 := by
    rw [h5]
    exact GroupedBalancedSignBottomTreeNodeInput67.input_pc t4 p4
  have a : OrdinarySteps image s 21 t1 := by
    rw [h1]
    exact GroupedBalancedSignBottomTreeSelectPtr67.select_steps s pc
  have b : OrdinarySteps image t1 4 t2 := by
    rw [h2]
    exact GroupedBalancedSignBottomTreeSelectCopy67.copy_steps
      t1 p1 src0 src1 dst0 dst1
  have c : OrdinarySteps image t2 12 t3 := by
    rw [h3]
    exact GroupedBalancedSignBottomTreePairPtr67.pair_steps t2 p2
  have d : OrdinarySteps image t3 4 t4 := by
    rw [h4]
    exact GroupedBalancedSignBottomTreePairLoad67.load_steps
      t3 p3 (by simpa using child0) child1 child2 child3
  have e : OrdinarySteps image t4 6 t5 := by
    rw [h5]
    exact GroupedBalancedSignBottomTreeNodeInput67.input_steps t4 p4
  have f := GroupedBalancedSignBottomTreeH4Query67.node_call hash t5 p5
  have ab := (OrdinarySteps.trace (hash := hash) a).trans
    (OrdinarySteps.trace (hash := hash) b)
  have abc := ab.trans (OrdinarySteps.trace (hash := hash) c)
  have abcd := abc.trans (OrdinarySteps.trace (hash := hash) d)
  have abcde := abcd.trans (OrdinarySteps.trace (hash := hash) e)
  have abcdef := abcde.trans f
  simpa only [Nat.reduceAdd] using abcdef
#print axioms parent_query_trace
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentTrace67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
theorem first_tick (hash : Hash)
    (s t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 : MachineState)
    (pc : s.pc = 0x1e94)
    (h1 : t1 = GroupedBalancedSignBottomTreeSelectPtr67.selectState s)
    (h2 : t2 = GroupedBalancedSignBottomTreeSelectCopy67.copyState t1)
    (h3 : t3 = GroupedBalancedSignBottomTreePairPtr67.pairState t2)
    (h4 : t4 = GroupedBalancedSignBottomTreePairLoad67.loadState t3)
    (h5 : t5 = GroupedBalancedSignBottomTreeNodeInput67.inputState t4)
    (h6 : t6 = writeHash
      (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5)
      (hash (hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t5))))
    (h7 : t7 = GroupedBalancedSignBottomTreeHashStorePtr67.storeState t6)
    (h8 : t8 = GroupedBalancedSignBottomTreeHashStoreCopy67.copyState t7)
    (h9 : t9 = GroupedBalancedSignBottomTreeParentAdvance67.advanceState t8)
    (h10 : t10 = GroupedBalancedSignBottomTreeParentControl67.branchState t9)
    (src0 : accessValid (t1.getReg .x6) 8 = true)
    (src1 : accessValid (t1.getReg .x6 + 8) 8 = true)
    (dst0 : accessValid (t1.getReg .x7) 8 = true)
    (dst1 : accessValid (t1.getReg .x7 + 8) 8 = true)
    (child0 : accessValid (t3.getReg .x7) 8 = true)
    (child1 : accessValid (t3.getReg .x7 + 8) 8 = true)
    (child2 : accessValid (t3.getReg .x7 + 16) 8 = true)
    (child3 : accessValid (t3.getReg .x7 + 24) 8 = true)
    (out0 : accessValid (t7.getReg .x7) 8 = true)
    (out1 : accessValid (t7.getReg .x7 + 8) 8 = true) :
    Trace hash image s 113 120 1 1 t10 := by
  have p5 : t5.pc = 0x1f50 := by
    rw [h5,h4,h3,h2,h1]
    exact GroupedBalancedSignBottomTreeNodeInput67.input_pc _
      (GroupedBalancedSignBottomTreePairLoad67.load_pc _
        (GroupedBalancedSignBottomTreePairPtr67.pair_pc _
          (GroupedBalancedSignBottomTreeSelectCopy67.copy_pc _
            (GroupedBalancedSignBottomTreeSelectPtr67.select_pc s pc))))
  have p6 : t6.pc = 0x1fd8 := by
    rw [h6,Keygen.hash_pc]
    rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_pc t5 p5]
    decide
  have p7 : t7.pc = 0x2008 := by
    rw [h7]
    exact GroupedBalancedSignBottomTreeHashStorePtr67.store_pc t6 p6
  have p8 : t8.pc = 0x2010 := by
    rw [h8]
    exact GroupedBalancedSignBottomTreeHashStoreCopy67.copy_pc t7 p7
  have p9 : t9.pc = 0x2054 := by
    rw [h9]
    exact GroupedBalancedSignBottomTreeParentAdvance67.advance_pc t8 p8
  have a : Trace hash image s 81 88 1 1 t6 := by
    rw [h6]
    exact GroupedBalancedSignBottomTreeParentTrace67.parent_query_trace
      hash s t1 t2 t3 t4 t5 pc h1 h2 h3 h4 h5
      src0 src1 dst0 dst1 child0 child1 child2 child3
  have b : OrdinarySteps image t6 12 t7 := by
    rw [h7]
    exact GroupedBalancedSignBottomTreeHashStorePtr67.store_steps t6 p6
  have c : OrdinarySteps image t7 2 t8 := by
    rw [h8]
    exact GroupedBalancedSignBottomTreeHashStoreCopy67.copy_steps
      t7 p7 out0 out1
  have d : OrdinarySteps image t8 17 t9 := by
    rw [h9]
    exact GroupedBalancedSignBottomTreeParentAdvance67.advance_steps t8 p8
  have e : OrdinarySteps image t9 1 t10 := by
    rw [h10]
    exact GroupedBalancedSignBottomTreeParentControl67.branch_steps t9 p9
  have ab := a.trans (OrdinarySteps.trace (hash := hash) b)
  have abc := ab.trans (OrdinarySteps.trace (hash := hash) c)
  have abcd := abc.trans (OrdinarySteps.trace (hash := hash) d)
  have abcde := abcd.trans (OrdinarySteps.trace (hash := hash) e)
  simpa only [Nat.reduceAdd] using abcde
#print axioms first_tick
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTick67
