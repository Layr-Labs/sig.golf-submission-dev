import SigGolfCandidate.Hypertree.BalancedPatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x15 0x80)
  let s := execInstrBr s (.ADDI .x15 .x15 0x600)
  let s := execInstrBr s (.LUI .x16 0x7070)
  let s := execInstrBr s (.ADDI .x16 .x16 0x707)
  let s := execInstrBr s (.SLLI .x17 .x16 32)
  execInstrBr s (.ADD .x16 .x16 .x17)

theorem setup_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = start+12) :
    OrdinarySteps image s 6 (setupState s) := by
  have c0 : instructionAt image (start+12) = some (.base (.LUI .x15 0x80)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨3,by decide⟩
  have c1 : instructionAt image (start+16) = some (.base (.ADDI .x15 .x15 0x600)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨4,by decide⟩
  have c2 : instructionAt image (start+20) = some (.base (.LUI .x16 0x7070)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨5,by decide⟩
  have c3 : instructionAt image (start+24) = some (.base (.ADDI .x16 .x16 0x707)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨6,by decide⟩
  have c4 : instructionAt image (start+28) = some (.base (.SLLI .x17 .x16 32)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨7,by decide⟩
  have c5 : instructionAt image (start+32) = some (.base (.ADD .x16 .x16 .x17)) := by
    simpa [patchInstructions, BitVec.add_assoc] using code.2 ⟨8,by decide⟩
  let s1 := execInstrBr s (.LUI .x15 0x80)
  let s2 := execInstrBr s1 (.ADDI .x15 .x15 0x600)
  let s3 := execInstrBr s2 (.LUI .x16 0x7070)
  let s4 := execInstrBr s3 (.ADDI .x16 .x16 0x707)
  let s5 := execInstrBr s4 (.SLLI .x17 .x16 32)
  let s6 := execInstrBr s5 (.ADD .x16 .x16 .x17)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x15 0x80)) 5
  · simpa only [fetch_at, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x15 .x15 0x600)) 4
  · have hp : s1.pc = start+16 := by simp [s1,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x16 0x7070)) 3
  · have hp : s2.pc = start+20 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x16 .x16 0x707)) 2
  · have hp : s3.pc = start+24 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x17 .x16 32)) 1
  · have hp : s4.pc = start+28 := by simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x16 .x16 .x17)) 0
  · have hp : s5.pc = start+32 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) : (setupState s).pc = s.pc+24 := by
  simp [setupState,execInstrBr,BitVec.add_assoc]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem setup_x15 (s : MachineState) :
    (setupState s).getReg .x15 = 0x80600 := by
  simp [setupState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem setup_x16 (s : MachineState) :
    (setupState s).getReg .x16 = 0x0707070707070707 := by
  simp [setupState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem setup_x12 (s : MachineState) :
    (setupState s).getReg .x12 = s.getReg .x12 := by
  simp [setupState,execInstrBr,MachineState.getReg_setReg_ne]

theorem setup_ra (s : MachineState) :
    (setupState s).getReg .x1 = s.getReg .x1 := by
  simp [setupState,execInstrBr,MachineState.getReg_setReg_ne]

theorem setup_sp (s : MachineState) :
    (setupState s).getReg .x2 = s.getReg .x2 := by
  simp [setupState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms setup_block
#print axioms setup_x15
#print axioms setup_x16
end SigGolfCandidate.Hypertree.Signing
