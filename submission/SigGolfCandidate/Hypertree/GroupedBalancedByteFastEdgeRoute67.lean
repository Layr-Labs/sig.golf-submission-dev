import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndex67

/-! The shared nine-instruction sibling-load tail on both Merkle sides. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeRoute67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def RouteCode (image : Image) (p : Word) (dst : BitVec 12) : Prop :=
  Keygen.instructionAt image p = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image (p+4) = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image (p+8) = some (.base (.LD .x7 .x28 0)) ∧
  Keygen.instructionAt image (p+12) = some (.base (.LD .x10 .x7 0)) ∧
  Keygen.instructionAt image (p+16) = some (.base (.LD .x11 .x7 8)) ∧
  Keygen.instructionAt image (p+20) = some (.base (.LUI .x7 0x80)) ∧
  Keygen.instructionAt image (p+24) = some (.base (.ADDI .x7 .x7 dst)) ∧
  Keygen.instructionAt image (p+28) = some (.base (.SD .x7 .x10 0)) ∧
  Keygen.instructionAt image (p+32) = some (.base (.SD .x7 .x11 8))

theorem right_code : RouteCode image 0x1808 0x520 := by
  unfold RouteCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem left_code : RouteCode image 0x185c 0x530 := by
  unfold RouteCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def routeState (s : MachineState) (dst : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 dst)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)

theorem route_block (p : Word) (dst : BitVec 12)
    (code : RouteCode image p dst)
    (s : MachineState) (pc : s.pc = p)
    (src0 : accessValid (s.getMem 0x81048) 8 = true)
    (src8 : accessValid (s.getMem 0x81048 + 8) 8 = true)
    (dst0 : accessValid ((0x80000 : Word) + signExtend12 dst) 8 = true)
    (dst8 : accessValid ((0x80000 : Word) + signExtend12 dst + 8) 8 = true) :
    OrdinarySteps image s 9 (routeState s dst) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 dst)
  let s8 := execInstrBr s7 (.SD .x7 .x10 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 8
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 7
  · have hp : s1.pc = p+4 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 6
  · have hp : s2.pc = p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 5
  · have hp : s3.pc = p+12 := by
      simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c3
  · have ptr : s3.getReg .x7 = s.getMem 0x81048 := by
      simp [s1,s2,s3,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq]
    simpa [s4,ordinaryStep,memoryArgumentsValid,ptr,signExtend12]
      using src0
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 4
  · have hp : s4.pc = p+16 := by
      simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c4
  · have ptr : s4.getReg .x7 = s.getMem 0x81048 := by
      simp [s1,s2,s3,s4,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [s5,ordinaryStep,memoryArgumentsValid,signExtend12,ptr]
      using src8
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 3
  · have hp : s5.pc = p+20 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 dst)) 2
  · have hp : s6.pc = p+24 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x10 0)) 1
  · have hp : s7.pc = p+28 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c7
  · have target : s7.getReg .x7 = (0x80000 : Word) + signExtend12 dst := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [s8,ordinaryStep,memoryArgumentsValid,signExtend12,target]
      using dst0
  apply OrdinarySteps.step s8 (execInstrBr s8 (.SD .x7 .x11 8)) _
    (.base (.SD .x7 .x11 8)) 0
  · have hp : s8.pc = p+32 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c8
  · have target : s8.getReg .x7 = (0x80000 : Word) + signExtend12 dst := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [ordinaryStep,memoryArgumentsValid,signExtend12,target]
      using dst8
  exact OrdinarySteps.refl _

theorem route_pc (s : MachineState) (dst : BitVec 12) :
    (routeState s dst).pc = s.pc + 36 := by
  simp [routeState,execInstrBr,BitVec.add_assoc]

theorem right_jump_code :
    Keygen.instructionAt image 0x182c = some (.base (.JAL .x0 84)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem right_jump (s : MachineState) (pc : s.pc = 0x182c) :
    OrdinarySteps image s 1 (execInstrBr s (.JAL .x0 84)) ∧
    (execInstrBr s (.JAL .x0 84)).pc = 0x1880 := by
  constructor
  · apply OrdinarySteps.step s _ _ (.base (.JAL .x0 84)) 0
    · simpa only [Keygen.fetch_at,pc] using right_jump_code
    · rfl
    exact OrdinarySteps.refl _
  · simp [execInstrBr,pc,signExtend21]

theorem right_route (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1808)
    (src0 : accessValid (s.getMem 0x81048) 8 = true)
    (src8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    Trace hash image s 10 10 0 0
      (execInstrBr (routeState s 0x520) (.JAL .x0 84)) ∧
    (execInstrBr (routeState s 0x520) (.JAL .x0 84)).pc = 0x1880 := by
  have first := route_block 0x1808 0x520 right_code s pc
    src0 src8 (by decide) (by decide)
  have midPC : (routeState s 0x520).pc = 0x182c := by
    rw [route_pc,pc]
    decide
  have second := right_jump (routeState s 0x520) midPC
  constructor
  · have whole := (OrdinarySteps.trace (hash := hash) first).trans
      (OrdinarySteps.trace (hash := hash) second.1)
    simpa using whole
  · exact second.2

theorem left_route (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x185c)
    (src0 : accessValid (s.getMem 0x81048) 8 = true)
    (src8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    Trace hash image s 9 9 0 0 (routeState s 0x530) ∧
    (routeState s 0x530).pc = 0x1880 := by
  have first := route_block 0x185c 0x530 left_code s pc
    src0 src8 (by decide) (by decide)
  constructor
  · exact first.trace
  · rw [route_pc,pc]
    decide

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeRoute67
