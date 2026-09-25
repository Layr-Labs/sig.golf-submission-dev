import SigGolfCandidate.Hypertree.VerifyHoistHeader
import SigGolfCandidate.Hypertree.VerifyChainHeaderDirect

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def EntryCode (image : Image) : Prop :=
  instructionAt image 0x14e8 = some (.base (.JAL .x0 1056)) ∧
  instructionAt image 0x1908 = some (.base (.ADDI .x30 .x10 0)) ∧
  instructionAt image 0x190c = some (.base (.BEQ .x6 .x0 24))

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.JAL .x0 1056)
  let s := execInstrBr s (.ADDI .x30 .x10 0)
  execInstrBr s (.BEQ .x6 .x0 24)

theorem entry_block (image : Image) (code : EntryCode image)
    (s : MachineState) (pc : s.pc = 0x14e8) :
    OrdinarySteps image s 3 (entryState s) := by
  obtain ⟨c0,c1,c2⟩ := code
  let s1 := execInstrBr s (.JAL .x0 1056)
  let s2 := execInstrBr s1 (.ADDI .x30 .x10 0)
  let s3 := execInstrBr s2 (.BEQ .x6 .x0 24)
  apply OrdinarySteps.step s s1 _ (.base (.JAL .x0 1056)) 2
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x30 .x10 0)) 1
  · have hp : s1.pc = 0x1908 := by norm_num [s1,execInstrBr,pc,signExtend21]; decide
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x6 .x0 24)) 0
  · have hp : s2.pc = 0x190c := by norm_num [s1,s2,execInstrBr,pc,signExtend21]; decide
    simpa only [fetch_at,hp] using c2
  · rfl
  exact OrdinarySteps.refl _

def FullCode (image : Image) : Prop :=
  instructionAt image 0x1924 = some (.base (.SD .x28 .x30 0)) ∧
  instructionAt image 0x1928 = some (.base (.ADDI .x31 .x0 7)) ∧
  instructionAt image 0x192c = some (.base (.JAL .x0 (-1024)))

def fullState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SD .x28 .x30 0)
  let s := execInstrBr s (.ADDI .x31 .x0 7)
  execInstrBr s (.JAL .x0 (-1024))

theorem full_block (image : Image) (code : FullCode image)
    (s : MachineState) (pc : s.pc = 0x1924)
    (stepPtr : s.getReg .x28 = 0x80438) :
    OrdinarySteps image s 3 (fullState s) := by
  obtain ⟨c0,c1,c2⟩ := code
  let s1 := execInstrBr s (.SD .x28 .x30 0)
  let s2 := execInstrBr s1 (.ADDI .x31 .x0 7)
  let s3 := execInstrBr s2 (.JAL .x0 (-1024))
  apply OrdinarySteps.step s s1 _ (.base (.SD .x28 .x30 0)) 2
  · simpa only [fetch_at,pc] using c0
  · simp [s1,ordinaryStep,memoryArgumentsValid,execInstrBr,stepPtr,
      accessValid,rangeValid,MEMORY_BYTES,signExtend12]
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x31 .x0 7)) 1
  · have hp : s1.pc = 0x1928 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.JAL .x0 (-1024))) 0
  · have hp : s2.pc = 0x192c := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  exact OrdinarySteps.refl _

theorem full_pc (s : MachineState) (pc : s.pc = 0x1924) :
    (fullState s).pc = 0x152c := by
  norm_num [fullState,execInstrBr,pc,signExtend21]
  decide

def HeaderJumpCode (image : Image) : Prop :=
  instructionAt image 0x15ec = some (.base (.JAL .x0 836))

theorem header_jump (image : Image) (code : HeaderJumpCode image)
    (s : MachineState) (pc : s.pc = 0x15ec) :
    OrdinarySteps image s 1 (execInstrBr s (.JAL .x0 836)) := by
  apply OrdinarySteps.step s _ _ (.base (.JAL .x0 836)) 0
  · simpa only [HeaderJumpCode,fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _

end SigGolfCandidate.Hypertree.Verifying.Hoist
