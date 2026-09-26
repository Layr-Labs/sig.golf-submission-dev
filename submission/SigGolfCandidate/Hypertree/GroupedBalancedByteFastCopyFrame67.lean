import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeRoute67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeUpdate67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyFrame67. -/
section
/-! Exact pointer/count update at the end of each upper Merkle edge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeUpdate67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def UpdateCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x1960 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1964 = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image 0x1968 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x196c = some (.base (.ADDI .x6 .x6 16)) ∧
  Keygen.instructionAt image 0x1970 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1974 = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image 0x1978 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x197c = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1980 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x1984 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x1988 = some (.base (.ADDI .x6 .x6 1)) ∧
  Keygen.instructionAt image 0x198c = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1990 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x1994 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x1998 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x199c = some (.base (.ADDI .x28 .x28 80)) ∧
  Keygen.instructionAt image 0x19a0 = some (.base (.LD .x6 .x28 0)) ∧
  Keygen.instructionAt image 0x19a4 = some (.base (.ADDI .x6 .x6 1)) ∧
  Keygen.instructionAt image 0x19a8 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x19ac = some (.base (.ADDI .x28 .x28 80)) ∧
  Keygen.instructionAt image 0x19b0 = some (.base (.SD .x28 .x6 0)) ∧
  Keygen.instructionAt image 0x19b4 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x19b8 = some (.base (.ADDI .x28 .x28 96)) ∧
  Keygen.instructionAt image 0x19bc = some (.base (.LD .x7 .x28 0)) ∧
  Keygen.instructionAt image 0x19c0 = some (.base (.BNE .x6 .x7 (-616)))

theorem concrete_code : UpdateCode image := by
  unfold UpdateCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def updateState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 16)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 96)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 (-616))

theorem update_block (s : MachineState) (pc : s.pc = 0x1960) :
    OrdinarySteps image s 25 (updateState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 16)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x48)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0)
  let s10 := execInstrBr s9 (.LD .x6 .x28 0)
  let s11 := execInstrBr s10 (.ADDI .x6 .x6 1)
  let s12 := execInstrBr s11 (.LUI .x28 0x81)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0)
  let s14 := execInstrBr s13 (.SD .x28 .x6 0)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 80)
  let s17 := execInstrBr s16 (.LD .x6 .x28 0)
  let s18 := execInstrBr s17 (.ADDI .x6 .x6 1)
  let s19 := execInstrBr s18 (.LUI .x28 0x81)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 80)
  let s21 := execInstrBr s20 (.SD .x28 .x6 0)
  let s22 := execInstrBr s21 (.LUI .x28 0x81)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 96)
  let s24 := execInstrBr s23 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 24
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 23
  · have hp : s1.pc = 0x1964 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 22
  · have hp : s2.pc = 0x1968 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 16)) 21
  · have hp : s3.pc = 0x196c := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 20
  · have hp : s4.pc = 0x1970 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x48)) 19
  · have hp : s5.pc = 0x1974 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 18
  · have hp : s6.pc = 0x1978 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s7.pc = 0x197c := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0)) 16
  · have hp : s8.pc = 0x1980 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x6 .x28 0)) 15
  · have hp : s9.pc = 0x1984 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x6 .x6 1)) 14
  · have hp : s10.pc = 0x1988 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x81)) 13
  · have hp : s11.pc = 0x198c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0)) 12
  · have hp : s12.pc = 0x1990 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x6 0)) 11
  · have hp : s13.pc = 0x1994 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 10
  · have hp : s14.pc = 0x1998 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 80)) 9
  · have hp : s15.pc = 0x199c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s16.pc = 0x19a0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x6 .x6 1)) 7
  · have hp : s17.pc = 0x19a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s18.pc = 0x19a8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 80)) 5
  · have hp : s19.pc = 0x19ac := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s20.pc = 0x19b0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s21.pc = 0x19b4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 96)) 2
  · have hp : s22.pc = 0x19b8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x7 .x28 0)) 1
  · have hp : s23.pc = 0x19bc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 _ _ (.base (.BNE .x6 .x7 (-616))) 0
  · have hp : s24.pc = 0x19c0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  exact OrdinarySteps.refl _

theorem update_pc (s : MachineState) (pc : s.pc = 0x1960) :
    (updateState s).pc =
      if (updateState s).getReg .x6 ≠ (updateState s).getReg .x7
      then 0x1758 else 0x19c4 := by
  simp [updateState,execInstrBr,pc,signExtend13,
    MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeUpdate67

end

/-! Memory frame for the verified RV64 word-copy loops. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

theorem copy_loop_frame (image : Image) (p : Word)
    (code : Keygen.CopyCode image p)
    (source destination total n : Nat) (s : MachineState)
    (inv : Keygen.CopyInvariant p source destination total n s)
    (sourceBound : source + 8 * total ≤ MEMORY_BYTES)
    (destinationBound : destination + 8 * total ≤ MEMORY_BYTES)
    (sourceAlign : source % 8 = 0)
    (destinationAlign : destination % 8 = 0)
    (a : Word)
    (outside : ∀ k < total, a ≠ BitVec.ofNat 64 (destination + 8*k)) :
    ∃ final, OrdinarySteps image s (6*n) final ∧
      Keygen.CopyInvariant p source destination total 0 final ∧
      final.getMem a = s.getMem a := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv, rfl⟩
  | succ n ih =>
      have access := Keygen.copy_accesses p source destination total n s
        inv sourceBound destinationBound sourceAlign destinationAlign
      have block := Keygen.copy_block image p code s
        (by simpa [Keygen.CopyInvariant] using inv.2.2.1)
        access.1 access.2
      have nextInv := Keygen.copy_invariant_next p source destination total
        n s inv
      obtain ⟨final, tail, done, frame⟩ := ih (Expansion.loopNext s) nextInv
      have firstFrame : (Expansion.loopNext s).getMem a = s.getMem a := by
        obtain ⟨nle,_,_,_,destReg,_⟩ := inv
        have different := outside (total - (n+1)) (by omega)
        rw [Expansion.loop_next_mem, destReg]
        simp only [if_neg different]
      refine ⟨final, ?_, done, frame.trans firstFrame⟩
      have path := Keygen.ordinary_trans image s (Expansion.loopNext s)
        final 6 (6*n) block tail
      simpa [Nat.mul_succ,Nat.add_comm,Nat.add_left_comm,
        Nat.add_assoc] using path

theorem setup_mem (s : MachineState) (src dst count : BitVec 12)
    (a : Word) :
    (GroupedBalancedByteFastCopies67.setupState s src dst count).getMem a =
      s.getMem a := by
  simp [GroupedBalancedByteFastCopies67.setupState,execInstrBr]

theorem run_copy_frame (hash : Hash) (s : MachineState)
    (p : Word) (src dst count : BitVec 12)
    (source destination total : Nat)
    (setup : GroupedBalancedByteFastCopies67.SetupCode
      GroupedBalancedByteFastCopies67.image p src dst count)
    (loop : Keygen.CopyCode GroupedBalancedByteFastCopies67.image (p+20))
    (pc : s.pc = p)
    (sourceReg :
      (GroupedBalancedByteFastCopies67.setupState s src dst count).getReg .x6 =
        BitVec.ofNat 64 source)
    (destinationReg :
      (GroupedBalancedByteFastCopies67.setupState s src dst count).getReg .x7 =
        BitVec.ofNat 64 destination)
    (countReg :
      (GroupedBalancedByteFastCopies67.setupState s src dst count).getReg .x10 =
        BitVec.ofNat 64 total)
    (positive : 0 < total) (size : total ≤ 2097152)
    (sourceBound : source + 8*total ≤ MEMORY_BYTES)
    (destinationBound : destination + 8*total ≤ MEMORY_BYTES)
    (sourceAlign : source % 8 = 0)
    (destinationAlign : destination % 8 = 0)
    (a : Word)
    (outside : ∀ k < total, a ≠ BitVec.ofNat 64 (destination + 8*k)) :
    ∃ final,
      Trace hash GroupedBalancedByteFastCopies67.image s
        (5+6*total) (5+6*total) 0 0 final ∧
      Keygen.CopyInvariant (p+20) source destination total 0 final ∧
      final.getMem a = s.getMem a := by
  let prepared := GroupedBalancedByteFastCopies67.setupState s src dst count
  have pre := GroupedBalancedByteFastCopies67.setup_block p src dst count
    setup s pc
  have inv : Keygen.CopyInvariant (p+20) source destination total total
      prepared := by
    refine ⟨Nat.le_refl _,size,?_,?_,?_,countReg⟩
    · simp [positive.ne',prepared,
        GroupedBalancedByteFastCopies67.setup_pc,pc]
    · simpa using sourceReg
    · simpa using destinationReg
  obtain ⟨final,loopTrace,done,frame⟩ := copy_loop_frame
    GroupedBalancedByteFastCopies67.image (p+20) loop
    source destination total total prepared inv
    sourceBound destinationBound sourceAlign destinationAlign a outside
  refine ⟨final,?_,done,frame.trans (setup_mem s src dst count a)⟩
  have path := (OrdinarySteps.trace (hash := hash) pre).trans
    (OrdinarySteps.trace (hash := hash) loopTrace)
  simpa [prepared,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using path

theorem witness_copy_frame (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x17dc) :
    ∃ final,
      Trace hash GroupedBalancedByteFastCopies67.image s
        17 17 0 0 final ∧ final.pc = 0x1808 ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  obtain ⟨final,path,inv,frame⟩ := run_copy_frame hash s
    0x17dc 0x500 0x530 2 0x80500 0x80530 2
    GroupedBalancedByteFastCopies67.witness_copy_code.1
    GroupedBalancedByteFastCopies67.witness_copy_code.2 pc
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) 0x81048
    (by intro k hk; interval_cases k <;> decide)
  refine ⟨final,by simpa using path,?_,frame⟩
  have h := inv.2.2.1
  simpa [Keygen.CopyInvariant] using h

theorem sibling_copy_frame (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1830) :
    ∃ final,
      Trace hash GroupedBalancedByteFastCopies67.image s
        17 17 0 0 final ∧ final.pc = 0x185c ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  obtain ⟨final,path,inv,frame⟩ := run_copy_frame hash s
    0x1830 0x500 0x520 2 0x80500 0x80520 2
    GroupedBalancedByteFastCopies67.sibling_copy_code.1
    GroupedBalancedByteFastCopies67.sibling_copy_code.2 pc
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by rw [GroupedBalancedByteFastCopies67.setup_reg];
        simp [signExtend12])
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) 0x81048
    (by intro k hk; interval_cases k <;> decide)
  refine ⟨final,by simpa using path,?_,frame⟩
  have h := inv.2.2.1
  simpa [Keygen.CopyInvariant] using h

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyFrame67
