import SigGolfCandidate.Hypertree.BalancedPatchSetup
import SigGolfCandidate.Hypertree.BalancedPatchBytes

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

def wordPass (s : MachineState) : MachineState :=
  flipChunk (flipChunk (flipChunk (flipChunk (flipChunk s 0) 8) 16) 24) 32

theorem wordPass_block (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (pc : s.pc = start+36)
    (base : s.getReg .x15 = 0x80600) :
    OrdinarySteps image s 15 (wordPass s) := by
  let s1 := flipChunk s 0
  let s2 := flipChunk s1 8
  let s3 := flipChunk s2 16
  let s4 := flipChunk s3 24
  let s5 := flipChunk s4 32
  have b0 : OrdinarySteps image s 3 s1 :=
    flipChunk_block image (start+36) 0 (patch_chunk_code image entry start forward back code 0)
      s pc (by rw [base]; decide)
  have b1 : OrdinarySteps image s1 3 s2 :=
    flipChunk_block image (start+48) 8 (patch_chunk_code image entry start forward back code 1)
      s1 (by simp [s1,flipChunk_pc,pc,BitVec.add_assoc])
      (by have h := (flipChunk_regs s 0).1; rw [h,base]; decide)
  have b2 : OrdinarySteps image s2 3 s3 :=
    flipChunk_block image (start+60) 16 (patch_chunk_code image entry start forward back code 2)
      s2 (by simp [s2,s1,flipChunk_pc,pc,BitVec.add_assoc])
      (by have h1 := (flipChunk_regs s1 8).1; have h0 := (flipChunk_regs s 0).1;
          rw [h1,h0,base]; decide)
  have b3 : OrdinarySteps image s3 3 s4 :=
    flipChunk_block image (start+72) 24 (patch_chunk_code image entry start forward back code 3)
      s3 (by simp [s3,s2,s1,flipChunk_pc,pc,BitVec.add_assoc])
      (by have h2 := (flipChunk_regs s2 16).1;
          have h1 := (flipChunk_regs s1 8).1; have h0 := (flipChunk_regs s 0).1;
          rw [h2,h1,h0,base]; decide)
  have b4 : OrdinarySteps image s4 3 s5 :=
    flipChunk_block image (start+84) 32 (patch_chunk_code image entry start forward back code 4)
      s4 (by simp [s4,s3,s2,s1,flipChunk_pc,pc,BitVec.add_assoc])
      (by have h3 := (flipChunk_regs s3 24).1;
          have h2 := (flipChunk_regs s2 16).1;
          have h1 := (flipChunk_regs s1 8).1; have h0 := (flipChunk_regs s 0).1;
          rw [h3,h2,h1,h0,base]; decide)
  change OrdinarySteps image s 15 s5
  exact Keygen.ordinary_trans image s _ _ 12 3
    (Keygen.ordinary_trans image s _ _ 9 3
      (Keygen.ordinary_trans image s _ _ 6 3
        (Keygen.ordinary_trans image s _ _ 3 3 b0 b1) b2) b3) b4

theorem wordPass_pc (s : MachineState) : (wordPass s).pc = s.pc+60 := by
  simp [wordPass,flipChunk_pc,BitVec.add_assoc]

theorem wordPass_regs (s : MachineState) :
    (wordPass s).getReg .x15 = s.getReg .x15 ∧
    (wordPass s).getReg .x16 = s.getReg .x16 ∧
    (wordPass s).getReg .x12 = s.getReg .x12 ∧
    (wordPass s).getReg .x10 = s.getReg .x10 ∧
    (wordPass s).getReg .x2 = s.getReg .x2 := by
  simp [wordPass, (flipChunk_regs _ _).1, (flipChunk_regs _ _).2.1,
    (flipChunk_regs _ _).2.2.1, (flipChunk_regs _ _).2.2.2.1,
    (flipChunk_regs _ _).2.2.2.2]

end SigGolfCandidate.Hypertree.Signing
