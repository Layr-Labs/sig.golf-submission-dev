import SigGolfCandidate.Hypertree.BalancedPatchBytes
import SigGolfCandidate.Hypertree.BalancedPatchTail
import SigGolfCandidate.Hypertree.Encoding

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def entryState (s : MachineState) (forward : BitVec 21) : MachineState :=
  execInstrBr s (.JAL .x0 forward)

theorem entry_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = entry) :
    OrdinarySteps image s 1 (entryState s forward) := by
  apply OrdinarySteps.step s _ _ (.base (.JAL .x0 forward)) 0
  · simpa only [fetch_at, pc] using code.1
  · rfl
  exact OrdinarySteps.refl _

theorem entry_pc (s : MachineState) (entry start : Word) (forward : BitVec 21)
    (pc : s.pc = entry) (offset : entry + signExtend21 forward = start) :
    (entryState s forward).pc = start := by
  simp [entryState, execInstrBr, pc, offset]

theorem entry_mem (s : MachineState) (forward : BitVec 21) (a : Word) :
    (entryState s forward).getMem a = s.getMem a := by
  simp [entryState, execInstrBr]

theorem entry_reg (s : MachineState) (forward : BitVec 21) (r : Reg) :
    (entryState s forward).getReg r = s.getReg r := by
  by_cases h : r = .x0
  · subst r
    simp only [entryState, execInstrBr, MachineState.getReg_setPC,
      MachineState.setReg, MachineState.getReg]
  · simp only [entryState, execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne s .x0 r _ (Ne.symm h)

def testState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x14 .x12 (-151))
  let s := execInstrBr s (.SRLI .x14 .x14 63)
  execInstrBr s (.BNE .x14 .x0 132)

def TestCode (image : Image) (start : Word) : Prop :=
  instructionAt image start = some (.base (.ADDI .x14 .x12 (-151))) ∧
  instructionAt image (start+4) = some (.base (.SRLI .x14 .x14 63)) ∧
  instructionAt image (start+8) = some (.base (.BNE .x14 .x0 132))

theorem patch_test_code (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back) : TestCode image start := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [patchInstructions] using code.2 ⟨0, by decide⟩
  · simpa [patchInstructions] using code.2 ⟨1, by decide⟩
  · simpa [patchInstructions] using code.2 ⟨2, by decide⟩

theorem test_block (image : Image) (start : Word) (code : TestCode image start)
    (s : MachineState) (pc : s.pc = start) :
    OrdinarySteps image s 3 (testState s) := by
  rcases code with ⟨c0,c1,c2⟩
  let s1 := execInstrBr s (.ADDI .x14 .x12 (-151))
  let s2 := execInstrBr s1 (.SRLI .x14 .x14 63)
  let s3 := execInstrBr s2 (.BNE .x14 .x0 132)
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x14 .x12 (-151))) 2
  · simpa only [fetch_at, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SRLI .x14 .x14 63)) 1
  · have hp : s1.pc = start+4 := by simp [s1,execInstrBr,pc]
    simpa only [fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BNE .x14 .x0 132)) 0
  · have hp : s2.pc = start+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [fetch_at,hp] using c2
  · rfl
  exact OrdinarySteps.refl _

theorem test_mem (s : MachineState) (a : Word) :
    (testState s).getMem a = s.getMem a := by
  simp [testState,execInstrBr]

theorem test_reg (s : MachineState) (r : Reg) (hr : r ≠ .x14) :
    (testState s).getReg r = s.getReg r := by
  have hr' : Reg.x14 ≠ r := Ne.symm hr
  simp only [testState, execInstrBr]
  split_ifs <;> simp [MachineState.getReg_setReg_ne, hr']

theorem test_flag (s : MachineState) (c : Nat) (bound : c ≤ 301)
    (sum : s.getReg .x12 = BitVec.ofNat 64 c) :
    (testState s).getReg .x14 = if c < 151 then 1 else 0 := by
  simp [testState,execInstrBr,MachineState.getReg_setReg_eq,sum]
  exact Reference.rawChecksum_branchBit c bound

theorem test_pc (s : MachineState) (c : Nat) (bound : c ≤ 301)
    (sum : s.getReg .x12 = BitVec.ofNat 64 c) :
    (testState s).pc = s.pc + (if c < 151 then 140 else 12) := by
  have flag := test_flag s c bound sum
  simp [testState, execInstrBr, MachineState.getReg_setReg_eq, sum] at flag
  simp [testState, execInstrBr, MachineState.getReg_setReg_eq,
    sum, flag, signExtend13, BitVec.add_assoc]
  split_ifs <;> rfl

end SigGolfCandidate.Hypertree.Signing
