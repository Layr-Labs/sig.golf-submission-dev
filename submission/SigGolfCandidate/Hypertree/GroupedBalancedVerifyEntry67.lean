import SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
import SigGolfCandidate.Hypertree.KeygenBlocks
import SigGolfCandidate.Hypertree.KeygenTrace
import RiscvZkvm.Rv64.Logic.MemRegion

/-! The official verifier loader and its first twelve RISC-V instructions. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67Byte.submission
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 56)
  execInstrBr s (.SD .x28 .x6 0)

private theorem entry_code :
    Keygen.instructionAt image 0x1000 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1004 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1008 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x100c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1010 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1014 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1018 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x101c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1020 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1024 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1028 = some (.base (.ADDI .x28 .x28 56)) ∧
    Keygen.instructionAt image 0x102c = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem entry_steps (s : MachineState) (pc : s.pc = 0x1000) :
    OrdinarySteps image s 12 (entryState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 48)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.ADDI .x6 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 56)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11⟩ := entry_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 11
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 10
  · have hp : s1.pc = 0x1004 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 9
  · have hp : s2.pc = 0x1008 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 8
  · have hp : s3.pc = 0x100c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 7
  · have hp : s4.pc = 0x1010 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s5.pc = 0x1014 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 48)) 5
  · have hp : s6.pc = 0x1018 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s7.pc = 0x101c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s8.pc = 0x1020 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s9.pc = 0x1024 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 56)) 1
  · have hp : s10.pc = 0x1028 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 (entryState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s11.pc = 0x102c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [entryState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,
      memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,
      MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_pc (s : MachineState) (pc : s.pc = 0x1000) :
    (entryState s).pc = 0x1030 := by
  simp [entryState,execInstrBr,pc]

theorem entry_words (s : MachineState) :
    (entryState s).getMem 0x81000 = 0 ∧
    (entryState s).getMem 0x81030 = 0 ∧
    (entryState s).getMem 0x81038 = 0 := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem entry_mem_other (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81000) (h30 : a ≠ 0x81030) (h38 : a ≠ 0x81038) :
    (entryState s).getMem a = s.getMem a := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  split_ifs <;> simp_all

theorem entry_tables (s : MachineState)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    GroupedBalancedVerifyByteContract67.Tables (entryState s) := by
  intro i hi
  let a : Word := BitVec.ofNat 64 (0xfff700+i)
  have halign : (alignToDword a).toNat = 8*((0xfff700+i)/8) := by
    have h := alignToDword_add_ofNat_of_aligned
      (base := 0#64) (i := 0xfff700+i) (by decide) (by simp; omega)
    have he : alignToDword a = BitVec.ofNat 64 (8*((0xfff700+i)/8)) := by
      simpa [a] using h
    rw [he,BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have h0 : alignToDword a ≠ 0x81000 := by
    intro he
    have hn := congrArg BitVec.toNat he
    rw [halign] at hn
    have hc : BitVec.toNat (0x81000 : Word) = 0x81000 := by decide
    rw [hc] at hn
    omega
  have h30 : alignToDword a ≠ 0x81030 := by
    intro he
    have hn := congrArg BitVec.toNat he
    rw [halign] at hn
    have hc : BitVec.toNat (0x81030 : Word) = 0x81030 := by decide
    rw [hc] at hn
    omega
  have h38 : alignToDword a ≠ 0x81038 := by
    intro he
    have hn := congrArg BitVec.toNat he
    rw [halign] at hn
    have hc : BitVec.toNat (0x81038 : Word) = 0x81038 := by decide
    rw [hc] at hn
    omega
  have frame := entry_mem_other s (alignToDword a) h0 h30 h38
  simpa only [GroupedBalancedVerifyByteContract67.Tables, MachineState.getByte,
    a, frame] using tables i hi

theorem entry_sp (s : MachineState) :
    (entryState s).getReg .x2 = s.getReg .x2 := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem loaded_sp (input : Input program.sizes .verify) (s : MachineState)
    (loaded : initialState program .verify input = some s) :
    s.getReg .x2 = 0xfff700 := by
  have hbase : Riscv.dataBase image = 0xfff700 := by
    simp [Riscv.dataBase,image,GroupedBalancedVerifyImage67Fast2Byte.image,
      GroupedBalancedDecoderByte67.data_length,MEMORY_BYTES]
  have h : s.getReg .x2 = BitVec.ofNat 64 (Riscv.dataBase image) := by
    unfold initialState at loaded
    rw [if_pos (GroupedBalancedProgram67Byte.admissible.2 .verify)] at loaded
    cases Option.some.inj loaded
    exact MachineState.getReg_setReg_eq (by decide)
  change s.getReg .x2 = BitVec.ofNat 64 0xfff700
  simpa only [hbase] using h

theorem loaded_entry (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 12 12 0 0 final ∧
      final.pc = 0x1030 ∧
      final.getMem 0x81000 = 0 ∧
      final.getMem 0x81030 = 0 ∧
      final.getMem 0x81038 = 0 ∧
      GroupedBalancedVerifyByteContract67.Tables final ∧
      final.getReg .x2 = 0xfff700 := by
  obtain ⟨initial,loaded,pc⟩ := initialState_exists program
    GroupedBalancedProgram67Byte.admissible .verify input
  refine ⟨initial,entryState initial,loaded,?_ , entry_pc initial pc,?_⟩
  · exact (entry_steps initial pc).trace
  · exact ⟨(entry_words initial).1,(entry_words initial).2.1,
      (entry_words initial).2.2,
      entry_tables initial (GroupedBalancedVerifyByteContract67.initial_tables input initial loaded),
      (entry_sp initial).trans (loaded_sp input initial loaded)⟩

#print axioms loaded_entry
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEntry67
