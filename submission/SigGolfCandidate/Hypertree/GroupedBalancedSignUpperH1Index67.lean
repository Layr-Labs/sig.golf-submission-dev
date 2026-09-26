import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSecretCopy67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Header67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Index67. -/
section
/-! Construct the paired-chain H1 address header from the group level and pair index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Header67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  execInstrBr s (.SD .x28 .x10 0)

private theorem header_code :
    Keygen.instructionAt image 0x17b0 = some (.base (.ADDI .x10 .x0 1)) ∧
    Keygen.instructionAt image 0x17b4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x17b8 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x17bc = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x17c0 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 0x17c4 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x17c8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x17cc = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x17d0 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x17d4 = some (.base (.SLLI .x11 .x11 24)) ∧
    Keygen.instructionAt image 0x17d8 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x17dc = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x17e0 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x17e4 = some (.base (.SD .x28 .x10 0)) := by decide

theorem header_steps (s : MachineState) (pc : s.pc = 0x17b0) :
    OrdinarySteps image s 14 (headerState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 1)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x30)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.SLLI .x11 .x11 24)
  let s11 := execInstrBr s10 (.ADD .x10 .x10 .x11)
  let s12 := execInstrBr s11 (.LUI .x28 0x80)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13⟩ := header_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 1)) 13
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 12
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 11
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 10
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · have haddr : s3.getReg .x28 = 0x81000 := by
      simp [s1,s2,s3,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s3.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s4 else none) = some s4
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 9
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 8
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 7
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,pc] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x30)) 6
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 5
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc] using c8
  · have haddr : s8.getReg .x28 = 0x81030 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s8.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s9 else none) = some s9
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s9 s10 _ (.base (.SLLI .x11 .x11 24)) 4
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADD .x10 .x10 .x11)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc] using c12
  · rfl
  apply OrdinarySteps.step s13 (headerState s) _ (.base (.SD .x28 .x10 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc] using c13
  · have haddr : s13.getReg .x28 = 0x80000 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s13.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (headerState s) else none) = some (headerState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem header_pc (s : MachineState) (pc : s.pc = 0x17b0) :
    (headerState s).pc = 0x17e8 := by
  simp [headerState,execInstrBr,pc]

theorem header_word (s : MachineState) :
    (headerState s).getMem 0x80000 =
      1 + (s.getMem 0x81000 <<< 8) + (s.getMem 0x81030 <<< 24) := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_frame (s : MachineState) (a : Word) (ha : a ≠ 0x80000) :
    (headerState s).getMem a = s.getMem a := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro h
  exact False.elim (ha h)

#print axioms header_steps
#print axioms header_pc
#print axioms header_word
#print axioms header_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Header67

end

/-! Copy the three 64-bit Merkle address words into the paired H1 input. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Index67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def indexState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  execInstrBr s (.SD .x28 .x11 0)

private theorem index_code :
    Keygen.instructionAt image 0x17e8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x17ec = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x17f0 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x17f4 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x17f8 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x17fc = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1800 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1804 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1808 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x180c = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1810 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1814 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1818 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x181c = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x1820 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1824 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1828 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x182c = some (.base (.SD .x28 .x11 0)) := by decide

theorem index_steps (s : MachineState) (pc : s.pc = 0x17e8) :
    OrdinarySteps image s 18 (indexState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 16)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x11 0)
  let s13 := execInstrBr s12 (.LUI .x28 0x81)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 24)
  let s15 := execInstrBr s14 (.LD .x11 .x28 0)
  let s16 := execInstrBr s15 (.LUI .x28 0x80)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 24)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17⟩ := index_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 17
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 16
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 15
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · have haddr : s2.getReg .x28 = 0x81008 := by
      simp [s1,s2,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s2.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s3 else none) = some s3
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 14
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 8)) 13
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x11 0)) 12
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · have haddr : s5.getReg .x28 = 0x80008 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s5.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s6 else none) = some s6
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 11
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,pc] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 16)) 10
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 9
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc] using c8
  · have haddr : s8.getReg .x28 = 0x81010 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s8.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s9 else none) = some s9
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 8
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 7
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 6
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc] using c11
  · have haddr : s11.getReg .x28 = 0x80010 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s11.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s12 else none) = some s12
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x81)) 5
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 24)) 4
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x11 .x28 0)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc] using c14
  · have haddr : s14.getReg .x28 = 0x81018 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s14.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s15 else none) = some s15
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 24)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc] using c16
  · rfl
  apply OrdinarySteps.step s17 (indexState s) _ (.base (.SD .x28 .x11 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc] using c17
  · have haddr : s17.getReg .x28 = 0x80018 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne,signExtend12]
    change (if accessValid (s17.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some (indexState s) else none) = some (indexState s)
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  exact OrdinarySteps.refl _

theorem index_pc (s : MachineState) (pc : s.pc = 0x17e8) :
    (indexState s).pc = 0x1830 := by
  simp [indexState,execInstrBr,pc]

theorem index_words (s : MachineState) (i : Fin 3) :
    (indexState s).getMem (Signing.wordAddress 0x80008 i.val) =
      s.getMem (Signing.wordAddress 0x81008 i.val) := by
  fin_cases i <;> simp [indexState,execInstrBr,Signing.wordAddress,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem index_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80008) (h1 : a ≠ 0x80010) (h2 : a ≠ 0x80018) :
    (indexState s).getMem a = s.getMem a := by
  change a ≠ 524296#64 at h0
  change a ≠ 524304#64 at h1
  change a ≠ 524312#64 at h2
  simp [indexState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h1,h2]

#print axioms index_steps
#print axioms index_pc
#print axioms index_words
#print axioms index_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1Index67
