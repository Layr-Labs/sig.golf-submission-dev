import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Run67

/-! Store the completed WOTS endpoint, increment the chain counter, and branch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointStore67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def address (s : MachineState) : Word :=
  (s.getMem 0x81030 <<< 4) + 0x80800

def storeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 0x81)
  let s := execInstrBr s (.ADDI .x10 .x10 0x800)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 8)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 67)
  execInstrBr s (.BNE .x6 .x7 0x1c68)

private theorem store_code :
    Keygen.instructionAt image 0x1ab0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1ab4 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x1ab8 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1abc = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x1ac0 = some (.base (.LUI .x10 0x81)) ∧
    Keygen.instructionAt image 0x1ac4 = some (.base (.ADDI .x10 .x10 0x800)) ∧
    Keygen.instructionAt image 0x1ac8 = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x1acc = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1ad0 = some (.base (.ADDI .x28 .x28 0x20)) ∧
    Keygen.instructionAt image 0x1ad4 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x1ad8 = some (.base (.LD .x11 .x28 8)) ∧
    Keygen.instructionAt image 0x1adc = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1ae0 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1ae4 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1ae8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1aec = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x1af0 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1af4 = some (.base (.ADDI .x7 .x0 67)) ∧
    Keygen.instructionAt image 0x1af8 = some (.base (.BNE .x6 .x7 0x1c68)) := by decide

theorem store_steps (s : MachineState) (pc : s.pc = 0x1ab0)
    (safe : accessValid (address s) 8 = true)
    (safeNext : accessValid (address s + 8) 8 = true) :
    OrdinarySteps image s 19 (storeState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x30)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 0x81)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 0x800)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 0x80)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0x20)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LD .x11 .x28 8)
  let s12 := execInstrBr s11 (.SD .x7 .x10 0)
  let s13 := execInstrBr s12 (.SD .x7 .x11 8)
  let s14 := execInstrBr s13 (.ADDI .x6 .x6 1)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 0x30)
  let s17 := execInstrBr s16 (.SD .x28 .x6 0)
  let s18 := execInstrBr s17 (.ADDI .x7 .x0 67)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18⟩ := store_code
  apply OrdinarySteps.step s (s1) _ (.base (.LUI .x28 0x81)) 18
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 (s2) _ (.base (.ADDI .x28 .x28 0x30)) 17
  · have hp : s1.pc = 0x1ab4 := by
      simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 (s3) _ (.base (.LD .x6 .x28 0)) 16
  · have hp : s2.pc = 0x1ab8 := by
      simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 (s4) _ (.base (.SLLI .x7 .x6 4)) 15
  · have hp : s3.pc = 0x1abc := by
      simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (s5) _ (.base (.LUI .x10 0x81)) 14
  · have hp : s4.pc = 0x1ac0 := by
      simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (s6) _ (.base (.ADDI .x10 .x10 0x800)) 13
  · have hp : s5.pc = 0x1ac4 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 (s7) _ (.base (.ADD .x7 .x7 .x10)) 12
  · have hp : s6.pc = 0x1ac8 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (s8) _ (.base (.LUI .x28 0x80)) 11
  · have hp : s7.pc = 0x1acc := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 (s9) _ (.base (.ADDI .x28 .x28 0x20)) 10
  · have hp : s8.pc = 0x1ad0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 (s10) _ (.base (.LD .x10 .x28 0)) 9
  · have hp : s9.pc = 0x1ad4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 (s11) _ (.base (.LD .x11 .x28 8)) 8
  · have hp : s10.pc = 0x1ad8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 (s12) _ (.base (.SD .x7 .x10 0)) 7
  · have hp : s11.pc = 0x1adc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,address,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne] using safe
  apply OrdinarySteps.step s12 (s13) _ (.base (.SD .x7 .x11 8)) 6
  · have hp : s12.pc = 0x1ae0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,address,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne] using safeNext
  apply OrdinarySteps.step s13 (s14) _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s13.pc = 0x1ae4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 (s15) _ (.base (.LUI .x28 0x81)) 4
  · have hp : s14.pc = 0x1ae8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 (s16) _ (.base (.ADDI .x28 .x28 0x30)) 3
  · have hp : s15.pc = 0x1aec := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 (s17) _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s16.pc = 0x1af0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 (s18) _ (.base (.ADDI .x7 .x0 67)) 1
  · have hp : s17.pc = 0x1af4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 (storeState s) _ (.base (.BNE .x6 .x7 0x1c68)) 0
  · have hp : s18.pc = 0x1af8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  exact OrdinarySteps.refl _

theorem store_pc (s : MachineState) :
    (storeState s).pc =
      if s.getMem 0x81030 + 1 = 67 then s.pc + 76
      else s.pc + 72 + signExtend13 0x1c68 := by
  simp [storeState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, BitVec.add_assoc]

theorem store_mem (s : MachineState) (a : Word) :
    (storeState s).getMem a =
      if a = 0x81030 then s.getMem 0x81030 + 1 else
      if a = address s + 8 then s.getMem 0x80028 else
      if a = address s then s.getMem 0x80020 else s.getMem a := by
  simp [storeState, address, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rfl

theorem address_eq (s : MachineState) (chain : Nat)
    (h : s.getMem 0x81030 = BitVec.ofNat 64 chain) :
    address s = BitVec.ofNat 64 (0x80800 + 16 * chain) := by
  unfold address
  rw [h, KeygenDomain.shift_ofNat]
  change BitVec.ofNat 64 (chain * 16) + BitVec.ofNat 64 0x80800 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem address_valid (s : MachineState) (chain : Nat)
    (h : s.getMem 0x81030 = BitVec.ofNat 64 chain) (hc : chain < 67) :
    accessValid (address s) 8 = true ∧
    accessValid (address s + 8) 8 = true := by
  rw [address_eq s chain h]
  have sum : BitVec.ofNat 64 (0x80800 + 16*chain) + 8 =
      BitVec.ofNat 64 (0x80800 + 16*chain + 8) :=
    (BitVec.ofNat_add _ _).symm
  rw [sum]
  have small : 0x80800 + 16*chain < 2^64 := by omega
  have smallNext : 0x80800 + 16*chain + 8 < 2^64 := by omega
  simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt smallNext]
  omega

theorem store_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81030) (h1 : a ≠ address s)
    (h2 : a ≠ address s + 8) :
    (storeState s).getMem a = s.getMem a := by
  rw [store_mem]
  split_ifs with e
  · exact False.elim (h0 e)
  · rfl

theorem store_counter (s : MachineState)
    (h : address s ≠ 0x81030) (h8 : address s + 8 ≠ 0x81030) :
    (storeState s).getMem 0x81030 = s.getMem 0x81030 + 1 := by
  rw [store_mem]
  simp [h, h8]

theorem store_stack (s : MachineState) :
    (storeState s).getReg .x2 = s.getReg .x2 := by
  simp [storeState,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms store_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointStore67
