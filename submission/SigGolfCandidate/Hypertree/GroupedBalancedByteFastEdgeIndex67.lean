import SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeHeader67


/-! Common Merkle-node body after the left/right child arrangement. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCore67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

/-- Four-word child copy, node query header, one-block hash, and two-word
result copy. The result-copy invariant fixes the exit at PC 0x1960. -/
theorem node_core (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1880) :
    ∃ final, Trace hash image s 80 87 1 1 final ∧
      Keygen.CopyInvariant 0x1948 0x80300 0x80500 2 0 final ∧
      final.pc = 0x1960 := by
  obtain ⟨copied, copyTrace, copyInv⟩ :=
    GroupedBalancedByteFastCopies67.child_copy hash s pc
  have copiedPC : copied.pc = 0x18ac := by
    have h := copyInv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  let ready := GroupedBalancedByteFastNodeHeader67.headerState copied
  have headerTrace := GroupedBalancedByteFastNodeHeader67.header_block
    copied copiedPC
  have fields := GroupedBalancedByteFastNodeHeader67.header_fields
    copied copiedPC
  let hashed := writeHash ready (hash (hashInput ready))
  have hashTrace := GroupedBalancedByteFastNodeQuery67.hash_trace
    hash ready fields
  have hashedPC := GroupedBalancedByteFastNodeQuery67.hash_pc
    hash ready fields
  obtain ⟨final, resultTrace, resultInv⟩ :=
    GroupedBalancedByteFastCopies67.result_copy hash hashed hashedPC
  have resultPC : final.pc = 0x1960 := by
    have h := resultInv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  refine ⟨final, ?_, resultInv, resultPC⟩
  have all := copyTrace.trans
    (headerTrace.trace.trans (hashTrace.trans resultTrace))
  simpa [image, GroupedBalancedByteFastCopies67.image,
    GroupedBalancedByteFastNodeHeader67.image,
    GroupedBalancedByteFastNodeQuery67.image] using all

theorem node_core_cycles_150 : 150 * 87 = 13050 := by decide

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCore67


/-! Exact index shift and left/right dispatch in one upper Merkle edge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndex67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def IndexCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x1758 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x175c = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x1760 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x1764 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1768 = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x176c = some (.base (.LD .x7 .x28 0)) ∧
  Keygen.instructionAt image 0x1770 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1774 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x1778 = some (.base (.LD .x10 .x28 0)) ∧
  Keygen.instructionAt image 0x177c = some (.base (.ANDI .x11 .x6 1)) ∧
  Keygen.instructionAt image 0x1780 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1784 = some (.base (.ADDI .x28 .x28 32)) ∧
  Keygen.instructionAt image 0x1788 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x178c = some (.base (.SRLI .x6 .x6 1)) ∧
  Keygen.instructionAt image 0x1790 = some (.base (.SLLI .x11 .x7 63)) ∧
  Keygen.instructionAt image 0x1794 = some (.base (.ADD .x6 .x6 .x11)) ∧
  Keygen.instructionAt image 0x1798 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x179c = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x17a0 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x17a4 = some (.base (.SRLI .x7 .x7 1)) ∧
  Keygen.instructionAt image 0x17a8 = some (.base (.SLLI .x11 .x10 63)) ∧
  Keygen.instructionAt image 0x17ac = some (.base (.ADD .x7 .x7 .x11)) ∧
  Keygen.instructionAt image 0x17b0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x17b4 = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x17b8 = some (.base (.SD .x28 .x7 0)) ∧
  Keygen.instructionAt image 0x17bc = some (.base (.SRLI .x10 .x10 1)) ∧
  Keygen.instructionAt image 0x17c0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x17c4 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x17c8 = some (.base (.SD .x28 .x10 0)) ∧
  Keygen.instructionAt image 0x17cc = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x17d0 = some (.base (.ADDI .x28 .x28 32)) ∧
  Keygen.instructionAt image 0x17d4 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x17d8 = some (.base (.BEQ .x6 .x0 88))

theorem concrete_code : IndexCode image := by
  unfold IndexCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def indexState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ANDI .x11 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.SLLI .x11 .x7 63)
  let s := execInstrBr s (.ADD .x6 .x6 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.SRLI .x7 .x7 1)
  let s := execInstrBr s (.SLLI .x11 .x10 63)
  let s := execInstrBr s (.ADD .x7 .x7 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.SRLI .x10 .x10 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  let s := execInstrBr s (.LD .x6 .x28 0)
  execInstrBr s (.BEQ .x6 .x0 88)

theorem index_block (s : MachineState) (pc : s.pc = 0x1758) :
    OrdinarySteps image s 33 (indexState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 16)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 24)
  let s9 := execInstrBr s8 (.LD .x10 .x28 0)
  let s10 := execInstrBr s9 (.ANDI .x11 .x6 1)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 32)
  let s13 := execInstrBr s12 (.SD .x28 .x11 0)
  let s14 := execInstrBr s13 (.SRLI .x6 .x6 1)
  let s15 := execInstrBr s14 (.SLLI .x11 .x7 63)
  let s16 := execInstrBr s15 (.ADD .x6 .x6 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 0x81)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 8)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.SRLI .x7 .x7 1)
  let s21 := execInstrBr s20 (.SLLI .x11 .x10 63)
  let s22 := execInstrBr s21 (.ADD .x7 .x7 .x11)
  let s23 := execInstrBr s22 (.LUI .x28 0x81)
  let s24 := execInstrBr s23 (.ADDI .x28 .x28 16)
  let s25 := execInstrBr s24 (.SD .x28 .x7 0)
  let s26 := execInstrBr s25 (.SRLI .x10 .x10 1)
  let s27 := execInstrBr s26 (.LUI .x28 0x81)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.SD .x28 .x10 0)
  let s30 := execInstrBr s29 (.LUI .x28 0x81)
  let s31 := execInstrBr s30 (.ADDI .x28 .x28 32)
  let s32 := execInstrBr s31 (.LD .x6 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 32
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 31
  · have hp : s1.pc = 0x175c := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 30
  · have hp : s2.pc = 0x1760 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 29
  · have hp : s3.pc = 0x1764 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 16)) 28
  · have hp : s4.pc = 0x1768 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 27
  · have hp : s5.pc = 0x176c := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 26
  · have hp : s6.pc = 0x1770 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 24)) 25
  · have hp : s7.pc = 0x1774 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x10 .x28 0)) 24
  · have hp : s8.pc = 0x1778 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ANDI .x11 .x6 1)) 23
  · have hp : s9.pc = 0x177c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 22
  · have hp : s10.pc = 0x1780 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 32)) 21
  · have hp : s11.pc = 0x1784 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x11 0)) 20
  · have hp : s12.pc = 0x1788 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SRLI .x6 .x6 1)) 19
  · have hp : s13.pc = 0x178c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SLLI .x11 .x7 63)) 18
  · have hp : s14.pc = 0x1790 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADD .x6 .x6 .x11)) 17
  · have hp : s15.pc = 0x1794 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x81)) 16
  · have hp : s16.pc = 0x1798 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 8)) 15
  · have hp : s17.pc = 0x179c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 14
  · have hp : s18.pc = 0x17a0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.SRLI .x7 .x7 1)) 13
  · have hp : s19.pc = 0x17a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SLLI .x11 .x10 63)) 12
  · have hp : s20.pc = 0x17a8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADD .x7 .x7 .x11)) 11
  · have hp : s21.pc = 0x17ac := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LUI .x28 0x81)) 10
  · have hp : s22.pc = 0x17b0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x28 .x28 16)) 9
  · have hp : s23.pc = 0x17b4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.SD .x28 .x7 0)) 8
  · have hp : s24.pc = 0x17b8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s25 s26 _ (.base (.SRLI .x10 .x10 1)) 7
  · have hp : s25.pc = 0x17bc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s26.pc = 0x17c0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 24)) 5
  · have hp : s27.pc = 0x17c4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.SD .x28 .x10 0)) 4
  · have hp : s28.pc = 0x17c8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s29.pc = 0x17cc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x28 .x28 32)) 2
  · have hp : s30.pc = 0x17d0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.LD .x6 .x28 0)) 1
  · have hp : s31.pc = 0x17d4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s32 _ _ (.base (.BEQ .x6 .x0 88)) 0
  · have hp : s32.pc = 0x17d8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  exact OrdinarySteps.refl _

theorem index_pc (s : MachineState) (pc : s.pc = 0x1758) :
    (indexState s).pc =
      if (indexState s).getReg .x6 = 0 then 0x1830 else 0x17dc := by
  simp [indexState,execInstrBr,pc,signExtend13,
    MachineState.getReg_setReg_ne]

theorem index_pointer_frame (s : MachineState) :
    (indexState s).getMem 0x81048 = s.getMem 0x81048 := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 16)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 24)
  let s9 := execInstrBr s8 (.LD .x10 .x28 0)
  let s10 := execInstrBr s9 (.ANDI .x11 .x6 1)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 32)
  let s13 := execInstrBr s12 (.SD .x28 .x11 0)
  let s14 := execInstrBr s13 (.SRLI .x6 .x6 1)
  let s15 := execInstrBr s14 (.SLLI .x11 .x7 63)
  let s16 := execInstrBr s15 (.ADD .x6 .x6 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 0x81)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 8)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.SRLI .x7 .x7 1)
  let s21 := execInstrBr s20 (.SLLI .x11 .x10 63)
  let s22 := execInstrBr s21 (.ADD .x7 .x7 .x11)
  let s23 := execInstrBr s22 (.LUI .x28 0x81)
  let s24 := execInstrBr s23 (.ADDI .x28 .x28 16)
  let s25 := execInstrBr s24 (.SD .x28 .x7 0)
  let s26 := execInstrBr s25 (.SRLI .x10 .x10 1)
  let s27 := execInstrBr s26 (.LUI .x28 0x81)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.SD .x28 .x10 0)
  let s30 := execInstrBr s29 (.LUI .x28 0x81)
  let s31 := execInstrBr s30 (.ADDI .x28 .x28 32)
  let s32 := execInstrBr s31 (.LD .x6 .x28 0)
  let s33 := execInstrBr s32 (.BEQ .x6 .x0 88)
  have h1 : s1.getMem 0x81048 = s.getMem 0x81048 := by
    simp [s1,execInstrBr]
  have h2 : s2.getMem 0x81048 = s1.getMem 0x81048 := by
    simp [s2,execInstrBr]
  have h3 : s3.getMem 0x81048 = s2.getMem 0x81048 := by
    simp [s3,execInstrBr]
  have h4 : s4.getMem 0x81048 = s3.getMem 0x81048 := by
    simp [s4,execInstrBr]
  have h5 : s5.getMem 0x81048 = s4.getMem 0x81048 := by
    simp [s5,execInstrBr]
  have h6 : s6.getMem 0x81048 = s5.getMem 0x81048 := by
    simp [s6,execInstrBr]
  have h7 : s7.getMem 0x81048 = s6.getMem 0x81048 := by
    simp [s7,execInstrBr]
  have h8 : s8.getMem 0x81048 = s7.getMem 0x81048 := by
    simp [s8,execInstrBr]
  have h9 : s9.getMem 0x81048 = s8.getMem 0x81048 := by
    simp [s9,execInstrBr]
  have h10 : s10.getMem 0x81048 = s9.getMem 0x81048 := by
    simp [s10,execInstrBr]
  have h11 : s11.getMem 0x81048 = s10.getMem 0x81048 := by
    simp [s11,execInstrBr]
  have h12 : s12.getMem 0x81048 = s11.getMem 0x81048 := by
    simp [s12,execInstrBr]
  have h13 : s13.getMem 0x81048 = s12.getMem 0x81048 := by
    have target : s12.getReg .x28 = 0x81020 := by
      simp [s12,s11,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simp [s13,execInstrBr,target,signExtend12,Expansion.mem_setMem]
  have h14 : s14.getMem 0x81048 = s13.getMem 0x81048 := by
    simp [s14,execInstrBr]
  have h15 : s15.getMem 0x81048 = s14.getMem 0x81048 := by
    simp [s15,execInstrBr]
  have h16 : s16.getMem 0x81048 = s15.getMem 0x81048 := by
    simp [s16,execInstrBr]
  have h17 : s17.getMem 0x81048 = s16.getMem 0x81048 := by
    simp [s17,execInstrBr]
  have h18 : s18.getMem 0x81048 = s17.getMem 0x81048 := by
    simp [s18,execInstrBr]
  have h19 : s19.getMem 0x81048 = s18.getMem 0x81048 := by
    have target : s18.getReg .x28 = 0x81008 := by
      simp [s18,s17,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simp [s19,execInstrBr,target,signExtend12,Expansion.mem_setMem]
  have h20 : s20.getMem 0x81048 = s19.getMem 0x81048 := by
    simp [s20,execInstrBr]
  have h21 : s21.getMem 0x81048 = s20.getMem 0x81048 := by
    simp [s21,execInstrBr]
  have h22 : s22.getMem 0x81048 = s21.getMem 0x81048 := by
    simp [s22,execInstrBr]
  have h23 : s23.getMem 0x81048 = s22.getMem 0x81048 := by
    simp [s23,execInstrBr]
  have h24 : s24.getMem 0x81048 = s23.getMem 0x81048 := by
    simp [s24,execInstrBr]
  have h25 : s25.getMem 0x81048 = s24.getMem 0x81048 := by
    have target : s24.getReg .x28 = 0x81010 := by
      simp [s24,s23,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simp [s25,execInstrBr,target,signExtend12,Expansion.mem_setMem]
  have h26 : s26.getMem 0x81048 = s25.getMem 0x81048 := by
    simp [s26,execInstrBr]
  have h27 : s27.getMem 0x81048 = s26.getMem 0x81048 := by
    simp [s27,execInstrBr]
  have h28 : s28.getMem 0x81048 = s27.getMem 0x81048 := by
    simp [s28,execInstrBr]
  have h29 : s29.getMem 0x81048 = s28.getMem 0x81048 := by
    have target : s28.getReg .x28 = 0x81018 := by
      simp [s28,s27,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simp [s29,execInstrBr,target,signExtend12,Expansion.mem_setMem]
  have h30 : s30.getMem 0x81048 = s29.getMem 0x81048 := by
    simp [s30,execInstrBr]
  have h31 : s31.getMem 0x81048 = s30.getMem 0x81048 := by
    simp [s31,execInstrBr]
  have h32 : s32.getMem 0x81048 = s31.getMem 0x81048 := by
    simp [s32,execInstrBr]
  have h33 : s33.getMem 0x81048 = s32.getMem 0x81048 := by
    simp [s33,execInstrBr]
  change s33.getMem 0x81048 = s.getMem 0x81048
  calc
    s33.getMem 0x81048 = s32.getMem 0x81048 := h33
    _ = s31.getMem 0x81048 := h32
    _ = s30.getMem 0x81048 := h31
    _ = s29.getMem 0x81048 := h30
    _ = s28.getMem 0x81048 := h29
    _ = s27.getMem 0x81048 := h28
    _ = s26.getMem 0x81048 := h27
    _ = s25.getMem 0x81048 := h26
    _ = s24.getMem 0x81048 := h25
    _ = s23.getMem 0x81048 := h24
    _ = s22.getMem 0x81048 := h23
    _ = s21.getMem 0x81048 := h22
    _ = s20.getMem 0x81048 := h21
    _ = s19.getMem 0x81048 := h20
    _ = s18.getMem 0x81048 := h19
    _ = s17.getMem 0x81048 := h18
    _ = s16.getMem 0x81048 := h17
    _ = s15.getMem 0x81048 := h16
    _ = s14.getMem 0x81048 := h15
    _ = s13.getMem 0x81048 := h14
    _ = s12.getMem 0x81048 := h13
    _ = s11.getMem 0x81048 := h12
    _ = s10.getMem 0x81048 := h11
    _ = s9.getMem 0x81048 := h10
    _ = s8.getMem 0x81048 := h9
    _ = s7.getMem 0x81048 := h8
    _ = s6.getMem 0x81048 := h7
    _ = s5.getMem 0x81048 := h6
    _ = s4.getMem 0x81048 := h5
    _ = s3.getMem 0x81048 := h4
    _ = s2.getMem 0x81048 := h3
    _ = s1.getMem 0x81048 := h2
    _ = s.getMem 0x81048 := h1

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndex67
