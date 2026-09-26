import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
/-! Actual RV64 endpoint copy and 67-chain counter update. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def address (s : MachineState) : Word := (s.getMem 0x81030 <<< 4) + 0x80800
def copyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 129)
  let s := execInstrBr s (.ADDI .x10 .x10 2048)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 8)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 67)
  execInstrBr s (.BNE .x6 .x7 0x1d38)

private theorem copy_code :
    Keygen.instructionAt image 0x12d0 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x12d4 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x12d8 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x12dc = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x12e0 = some (.base (.LUI .x10 129)) ∧
    Keygen.instructionAt image 0x12e4 = some (.base (.ADDI .x10 .x10 2048)) ∧
    Keygen.instructionAt image 0x12e8 = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x12ec = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x12f0 = some (.base (.ADDI .x28 .x28 32)) ∧
    Keygen.instructionAt image 0x12f4 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x12f8 = some (.base (.LD .x11 .x28 8)) ∧
    Keygen.instructionAt image 0x12fc = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1300 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1304 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1308 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x130c = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1310 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1314 = some (.base (.ADDI .x7 .x0 67)) ∧
    Keygen.instructionAt image 0x1318 = some (.base (.BNE .x6 .x7 0x1d38)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem copy_steps (s : MachineState) (pc : s.pc = 0x12d0)
    (safe : accessValid (address s) 8 = true)
    (safeNext : accessValid (address s + 8) 8 = true) :
    OrdinarySteps image s 19 (copyState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 48)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 129)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 2048)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 128)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 32)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LD .x11 .x28 8)
  let s12 := execInstrBr s11 (.SD .x7 .x10 0)
  let s13 := execInstrBr s12 (.SD .x7 .x11 8)
  let s14 := execInstrBr s13 (.ADDI .x6 .x6 1)
  let s15 := execInstrBr s14 (.LUI .x28 129)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 48)
  let s17 := execInstrBr s16 (.SD .x28 .x6 0)
  let s18 := execInstrBr s17 (.ADDI .x7 .x0 67)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18⟩ := copy_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 18
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 48)) 17
  · have hp : s1.pc = 0x12d4 := by
      simp [s1,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 16
  · have hp : s2.pc = 0x12d8 := by
      simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 15
  · have hp : s3.pc = 0x12dc := by
      simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 129)) 14
  · have hp : s4.pc = 0x12e0 := by
      simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 2048)) 13
  · have hp : s5.pc = 0x12e4 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x10)) 12
  · have hp : s6.pc = 0x12e8 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 128)) 11
  · have hp : s7.pc = 0x12ec := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 32)) 10
  · have hp : s8.pc = 0x12f0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 9
  · have hp : s9.pc = 0x12f4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x11 .x28 8)) 8
  · have hp : s10.pc = 0x12f8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x7 .x10 0)) 7
  · have hp : s11.pc = 0x12fc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,safe,address,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [address] using safe
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x7 .x11 8)) 6
  · have hp : s12.pc = 0x1300 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,safeNext,address,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [address] using safeNext
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s13.pc = 0x1304 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 129)) 4
  · have hp : s14.pc = 0x1308 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 48)) 3
  · have hp : s15.pc = 0x130c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s16.pc = 0x1310 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x7 .x0 67)) 1
  · have hp : s17.pc = 0x1314 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 (copyState s) _ (.base (.BNE .x6 .x7 0x1d38)) 0
  · have hp : s18.pc = 0x1318 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  exact OrdinarySteps.refl _

theorem copy_pc (s : MachineState) (pc : s.pc = 0x12d0) :
    (copyState s).pc =
      if s.getMem 0x81030 + 1 = 67 then 0x131c else 0x1050 := by
  simp [copyState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem copy_counter (s : MachineState) :
    (copyState s).getMem 0x81030 = s.getMem 0x81030 + 1 := by
  simp [copyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_x19 (s : MachineState) :
    (copyState s).getReg .x19 = s.getReg .x19 := by
  simp [copyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem copy_mem (s : MachineState) (a : Word) :
    (copyState s).getMem a =
      if a = 0x81030 then s.getMem 0x81030 + 1 else
      if a = address s + 8 then s.getMem 0x80028 else
      if a = address s then s.getMem 0x80020 else s.getMem a := by
  simp [copyState,address,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  rfl

theorem address_eq (s : MachineState) (n : Nat)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    address s = BitVec.ofNat 64 (0x80800+16*n) := by
  unfold address
  rw [counter,KeygenDomain.shift_ofNat]
  change BitVec.ofNat 64 (n*16) + BitVec.ofNat 64 0x80800 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem address_safe (s : MachineState) (n : Nat) (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    accessValid (address s) 8 = true ∧
    accessValid (address s+8) 8 = true := by
  rw [address_eq s n counter]
  have sum : BitVec.ofNat 64 (0x80800+16*n) + 8 =
      BitVec.ofNat 64 (0x80800+16*n+8) :=
    (BitVec.ofNat_add _ _).symm
  rw [sum]
  have small : 0x80800+16*n < 2^64 := by omega
  have smallNext : 0x80800+16*n+8 < 2^64 := by omega
  simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt smallNext]
  omega

#print axioms copy_steps
#print axioms copy_pc
#print axioms copy_mem
#print axioms address_safe
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointCopy67
