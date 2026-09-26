import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairLoad67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairPtrLoop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def pairState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 5)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.LD .x10 .x28 0)
  execInstrBr s (.ADD .x7 .x7 .x10)
theorem pair_steps (s : MachineState) (pc : s.pc = 0x1f08) :
    OrdinarySteps image s 8 (pairState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xd8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 5)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0xc0)
  let s7 := execInstrBr s6 (.LD .x10 .x28 0)
  have c0 : Keygen.instructionAt image 0x1f08 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1f0c = some (.base (.ADDI .x28 .x28 0xd8)) := by decide
  have c2 : Keygen.instructionAt image 0x1f10 = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1f14 = some (.base (.SLLI .x7 .x6 5)) := by decide
  have c4 : Keygen.instructionAt image 0x1f18 = some (.base (.LUI .x28 0x81)) := by decide
  have c5 : Keygen.instructionAt image 0x1f1c = some (.base (.ADDI .x28 .x28 0xc0)) := by decide
  have c6 : Keygen.instructionAt image 0x1f20 = some (.base (.LD .x10 .x28 0)) := by decide
  have c7 : Keygen.instructionAt image 0x1f24 = some (.base (.ADD .x7 .x7 .x10)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xd8)) 6
  · have hp : s1.pc = 0x1f0c := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x1f10 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [pairState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 5)) 4
  · have hp : s3.pc = 0x1f14 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s4.pc = 0x1f18 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0xc0)) 2
  · have hp : s5.pc = 0x1f1c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x10 .x28 0)) 1
  · have hp : s6.pc = 0x1f20 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [pairState,s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 (pairState s) _ (.base (.ADD .x7 .x7 .x10)) 0
  · have hp : s7.pc = 0x1f24 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _
theorem pair_pc (s : MachineState) (pc : s.pc = 0x1f08) : (pairState s).pc = 0x1f28 := by
  simp [pairState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms pair_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairPtrLoop67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentTick67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
theorem inner_tick (hash : Hash)
    (s t1 t2 t3 t4 t5 t6 t7 t8 : MachineState)
    (pc : s.pc = 0x1f08)
    (h1 : t1 = GroupedBalancedSignBottomTreePairPtrLoop67.pairState s)
    (h2 : t2 = GroupedBalancedSignBottomTreePairLoad67.loadState t1)
    (h3 : t3 = GroupedBalancedSignBottomTreeNodeInput67.inputState t2)
    (h4 : t4 = writeHash
      (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t3)
      (hash (hashInput (GroupedBalancedSignBottomTreeH4Prelude67.preludeState t3))))
    (h5 : t5 = GroupedBalancedSignBottomTreeHashStorePtr67.storeState t4)
    (h6 : t6 = GroupedBalancedSignBottomTreeHashStoreCopy67.copyState t5)
    (h7 : t7 = GroupedBalancedSignBottomTreeParentAdvance67.advanceState t6)
    (h8 : t8 = GroupedBalancedSignBottomTreeParentControl67.branchState t7)
    (child0 : accessValid (t1.getReg .x7) 8 = true)
    (child1 : accessValid (t1.getReg .x7 + 8) 8 = true)
    (child2 : accessValid (t1.getReg .x7 + 16) 8 = true)
    (child3 : accessValid (t1.getReg .x7 + 24) 8 = true)
    (out0 : accessValid (t5.getReg .x7) 8 = true)
    (out1 : accessValid (t5.getReg .x7 + 8) 8 = true) :
    Trace hash image s 84 91 1 1 t8 := by
  have p1 : t1.pc = 0x1f28 := by
    rw [h1]
    exact GroupedBalancedSignBottomTreePairPtrLoop67.pair_pc s pc
  have p2 : t2.pc = 0x1f38 := by
    rw [h2]
    exact GroupedBalancedSignBottomTreePairLoad67.load_pc t1 p1
  have p3 : t3.pc = 0x1f50 := by
    rw [h3]
    exact GroupedBalancedSignBottomTreeNodeInput67.input_pc t2 p2
  have p4 : t4.pc = 0x1fd8 := by
    rw [h4,Keygen.hash_pc]
    rw [GroupedBalancedSignBottomTreeH4Prelude67.prelude_pc t3 p3]
    decide
  have p5 : t5.pc = 0x2008 := by
    rw [h5]
    exact GroupedBalancedSignBottomTreeHashStorePtr67.store_pc t4 p4
  have p6 : t6.pc = 0x2010 := by
    rw [h6]
    exact GroupedBalancedSignBottomTreeHashStoreCopy67.copy_pc t5 p5
  have p7 : t7.pc = 0x2054 := by
    rw [h7]
    exact GroupedBalancedSignBottomTreeParentAdvance67.advance_pc t6 p6
  have a : OrdinarySteps image s 8 t1 := by
    rw [h1]
    exact GroupedBalancedSignBottomTreePairPtrLoop67.pair_steps s pc
  have b : OrdinarySteps image t1 4 t2 := by
    rw [h2]
    exact GroupedBalancedSignBottomTreePairLoad67.load_steps
      t1 p1 (by simpa using child0) child1 child2 child3
  have c : OrdinarySteps image t2 6 t3 := by
    rw [h3]
    exact GroupedBalancedSignBottomTreeNodeInput67.input_steps t2 p2
  have d : Trace hash image t3 34 41 1 1 t4 := by
    rw [h4]
    exact GroupedBalancedSignBottomTreeH4Query67.node_call hash t3 p3
  have e : OrdinarySteps image t4 12 t5 := by
    rw [h5]
    exact GroupedBalancedSignBottomTreeHashStorePtr67.store_steps t4 p4
  have f : OrdinarySteps image t5 2 t6 := by
    rw [h6]
    exact GroupedBalancedSignBottomTreeHashStoreCopy67.copy_steps
      t5 p5 out0 out1
  have g : OrdinarySteps image t6 17 t7 := by
    rw [h7]
    exact GroupedBalancedSignBottomTreeParentAdvance67.advance_steps t6 p6
  have j : OrdinarySteps image t7 1 t8 := by
    rw [h8]
    exact GroupedBalancedSignBottomTreeParentControl67.branch_steps t7 p7
  have ab := (OrdinarySteps.trace (hash := hash) a).trans
    (OrdinarySteps.trace (hash := hash) b)
  have abc := ab.trans (OrdinarySteps.trace (hash := hash) c)
  have abcd := abc.trans d
  have abcde := abcd.trans (OrdinarySteps.trace (hash := hash) e)
  have abcdef := abcde.trans (OrdinarySteps.trace (hash := hash) f)
  have abcdefg := abcdef.trans (OrdinarySteps.trace (hash := hash) g)
  have abcdefgj := abcdefg.trans (OrdinarySteps.trace (hash := hash) j)
  simpa only [Nat.reduceAdd] using abcdefgj
#print axioms inner_tick
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentTick67
