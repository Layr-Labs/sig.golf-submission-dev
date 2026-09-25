import SigGolfCandidate.Hypertree.BalancedPatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def finishState (s : MachineState) (back : BitVec 21) : MachineState :=
  let s := execInstrBr s (.ADDI .x14 .x0 301)
  let s := execInstrBr s (.SUB .x12 .x14 .x12)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  execInstrBr s (.JAL .x0 back)

def skipState (s : MachineState) (back : BitVec 21) : MachineState :=
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  execInstrBr s (.JAL .x0 back)

theorem finish_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = start+132) :
    OrdinarySteps image s 4 (finishState s back) := by
  have c0 : instructionAt image (start+132) = some (.base (.ADDI .x14 .x0 301)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨33,by decide⟩
  have c1 : instructionAt image (start+136) = some (.base (.SUB .x12 .x14 .x12)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨34,by decide⟩
  have c2 : instructionAt image (start+140) = some (.base (.ANDI .x13 .x12 7)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨35,by decide⟩
  have c3 : instructionAt image (start+144) = some (.base (.JAL .x0 back)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨36,by decide⟩
  let s1 := execInstrBr s (.ADDI .x14 .x0 301)
  let s2 := execInstrBr s1 (.SUB .x12 .x14 .x12)
  let s3 := execInstrBr s2 (.ANDI .x13 .x12 7)
  let s4 := execInstrBr s3 (.JAL .x0 back)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x14 .x0 301)) 3
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SUB .x12 .x14 .x12)) 2
  · have hp : s1.pc = start+136 := by simp [s1,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ANDI .x13 .x12 7)) 1
  · have hp : s2.pc = start+140 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.JAL .x0 back)) 0
  · have hp : s3.pc = start+144 := by simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c3
  · rfl
  exact OrdinarySteps.refl _

theorem skip_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = start+140) :
    OrdinarySteps image s 2 (skipState s back) := by
  have c0 : instructionAt image (start+140) = some (.base (.ANDI .x13 .x12 7)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨35,by decide⟩
  have c1 : instructionAt image (start+144) = some (.base (.JAL .x0 back)) := by
    simpa [patchInstructions,BitVec.add_assoc] using code.2 ⟨36,by decide⟩
  let s1 := execInstrBr s (.ANDI .x13 .x12 7)
  let s2 := execInstrBr s1 (.JAL .x0 back)
  apply OrdinarySteps.step s s1 _ (.base (.ANDI .x13 .x12 7)) 1
  · simpa only [fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.JAL .x0 back)) 0
  · have hp : s1.pc = start+144 := by simp [s1,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem finish_pc (s : MachineState) (entry start : Word) (back : BitVec 21)
    (pc : s.pc = start+132)
    (returnPC : start+144+signExtend21 back = entry+4) :
    (finishState s back).pc = entry+4 := by
  simpa [finishState,execInstrBr,pc,BitVec.add_assoc] using returnPC

theorem skip_pc (s : MachineState) (entry start : Word) (back : BitVec 21)
    (pc : s.pc = start+140)
    (returnPC : start+144+signExtend21 back = entry+4) :
    (skipState s back).pc = entry+4 := by
  simpa [skipState,execInstrBr,pc,BitVec.add_assoc] using returnPC

theorem finish_x12 (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x12 = 301#64 - s.getReg .x12 := by
  simp [finishState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem finish_checksum (s : MachineState) (back : BitVec 21) (c : Nat)
    (hc : c ≤ 301) (sum : s.getReg .x12 = BitVec.ofNat 64 c) :
    (finishState s back).getReg .x12 = BitVec.ofNat 64 (301-c) := by
  rw [finish_x12,sum]
  exact BitVec.ofNat_sub_ofNat_of_le 301 c (by omega) hc

theorem finish_x13 (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x13 = (301#64 - s.getReg .x12) &&& 7#64 := by
  simp [finishState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem skip_x12 (s : MachineState) (back : BitVec 21) :
    (skipState s back).getReg .x12 = s.getReg .x12 := by
  simp [skipState,execInstrBr,MachineState.getReg_setReg_ne]

theorem skip_x13 (s : MachineState) (back : BitVec 21) :
    (skipState s back).getReg .x13 = s.getReg .x12 &&& 7#64 := by
  simp [skipState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem finish_mem (s : MachineState) (back : BitVec 21) (a : Word) :
    (finishState s back).getMem a = s.getMem a := by
  simp [finishState,execInstrBr]

theorem skip_mem (s : MachineState) (back : BitVec 21) (a : Word) :
    (skipState s back).getMem a = s.getMem a := by
  simp [skipState,execInstrBr]

theorem finish_ra (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x1 = s.getReg .x1 := by
  simp [finishState,execInstrBr,MachineState.getReg_setReg_ne]

theorem finish_sp (s : MachineState) (back : BitVec 21) :
    (finishState s back).getReg .x2 = s.getReg .x2 := by
  simp [finishState,execInstrBr,MachineState.getReg_setReg_ne]

theorem skip_ra (s : MachineState) (back : BitVec 21) :
    (skipState s back).getReg .x1 = s.getReg .x1 := by
  simp [skipState,execInstrBr,MachineState.getReg_setReg_ne]

theorem skip_sp (s : MachineState) (back : BitVec 21) :
    (skipState s back).getReg .x2 = s.getReg .x2 := by
  simp [skipState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms finish_block
#print axioms skip_block
#print axioms finish_checksum
end SigGolfCandidate.Hypertree.Signing
