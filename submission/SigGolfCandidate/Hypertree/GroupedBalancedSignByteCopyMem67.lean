import SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
import RiscvZkvm.Rv64.Logic.WordOps
import RiscvZkvm.Rv64.Bytes
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopy67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67

theorem getWord32_setWord32_same (s : MachineState) (addr : Word) (v : BitVec 32) :
    (s.setWord32 addr v).getWord32 addr = v := by
  rw [getWord32_eq, setWord32_eq, MachineState.getMem_setMem_eq]
  apply extractWord32_replaceWord32_same _ ⟨(byteOffset addr) / 4, by
    have hb := byteOffset_lt_8 (addr := addr)
    omega⟩ _

theorem getByte_setWord32_ne (s : MachineState) (writeAddr readAddr : Word)
    (v : BitVec 32) (hne : alignToDword readAddr ≠ alignToDword writeAddr) :
    (s.setWord32 writeAddr v).getByte readAddr = s.getByte readAddr := by
  simp only [MachineState.getByte, setWord32_eq]
  rw [MachineState.getMem_setMem_ne hne]

theorem getWord32_setReg (s : MachineState) (r : Reg) (v addr : Word) :
    (s.setReg r v).getWord32 addr = s.getWord32 addr := by
  simp [MachineState.getWord32, MachineState.getMem_setReg]
theorem getWord32_setPC (s : MachineState) (v addr : Word) :
    (s.setPC v).getWord32 addr = s.getWord32 addr := by
  simp [MachineState.getWord32, MachineState.getMem_setPC]

theorem getWord32_bne (s : MachineState) (addr : Word) :
    (execInstrBr s (.BNE .x18 .x0 (-32))).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr]
  split_ifs <;> simp only [getWord32_setPC]
theorem getWord32_addi (s : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (addr : Word) :
    (execInstrBr s (.ADDI rd rs imm)).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr, getWord32_setReg, getWord32_setPC]

theorem getWord32_lbu (s : MachineState) (rd base : Reg)
    (addr : Word) :
    (execInstrBr s (.LBU rd base 0)).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr, getWord32_setReg, getWord32_setPC]
theorem getWord32_slli (s : MachineState) (rd base : Reg)
    (imm : BitVec 6) (addr : Word) :
    (execInstrBr s (.SLLI rd base imm)).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr, getWord32_setReg, getWord32_setPC]
theorem getWord32_add (s : MachineState) (rd x y : Reg)
    (addr : Word) :
    (execInstrBr s (.ADD rd x y)).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr, getWord32_setReg, getWord32_setPC]
theorem getWord32_lw (s : MachineState) (rd base : Reg)
    (addr : Word) :
    (execInstrBr s (.LW rd base 0)).getWord32 addr = s.getWord32 addr := by
  simp only [execInstrBr, getWord32_setReg, getWord32_setPC]

private theorem trunc_sign (v : BitVec 32) :
    (v.signExtend 64).truncate 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  simp only [BitVec.truncate, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_signExtend]
  simp [hi, hi64]

theorem copyBody_output_word (s : MachineState) :
    (copyBody s).getWord32 (s.getReg .x11) =
      s.getWord32 (s.getReg .x17 + (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2)) := by
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s5
    (.ADDI .x10 .x10 1)) (.ADDI .x11 .x11 4))
    (.ADDI .x18 .x18 (-1))) (.BNE .x18 .x0 (-32))).getWord32 _ = _
  rw [getWord32_bne, getWord32_addi, getWord32_addi, getWord32_addi]
  have hptr : s4.getReg .x11 = s.getReg .x11 := by
    simp [s1,s2,s3,s4,execInstrBr,MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have haddr : s3.getReg .x21 =
      s.getReg .x17 + (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2) := by
    simpa [s1,s2,s3] using
      (copy_body_table_address s)
  have hmem : s3.getWord32 (s.getReg .x17 +
      (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2)) =
      s.getWord32 (s.getReg .x17 +
      (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2)) := by
    simp only [s3, getWord32_add, s2, getWord32_slli, s1, getWord32_lbu]
  have hsrc : s4.getReg .x22 =
      BitVec.signExtend 64 (s.getWord32 (s.getReg .x17 +
        (BitVec.setWidth 64 (s.getByte (s.getReg .x10)) <<< 2))) := by
    simp [s4, execInstrBr, MachineState.getReg_setReg_eq, haddr, signExtend12,
      hmem]
  change s5.getWord32 (s.getReg .x11) = _
  simp only [s5, execInstrBr, hptr, getWord32_setPC]
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
  simp [getWord32_setWord32_same]
  rw [hsrc]
  exact trunc_sign _

private theorem getByte_setReg (s : MachineState) (r : Reg) (v addr : Word) :
    (s.setReg r v).getByte addr = s.getByte addr := by
  simp [MachineState.getByte, MachineState.getMem_setReg]
private theorem getByte_setPC (s : MachineState) (v addr : Word) :
    (s.setPC v).getByte addr = s.getByte addr := by
  simp [MachineState.getByte, MachineState.getMem_setPC]
private theorem getByte_bne (s : MachineState) (addr : Word) :
    (execInstrBr s (.BNE .x18 .x0 (-32))).getByte addr = s.getByte addr := by
  simp only [execInstrBr]
  split_ifs <;> simp only [getByte_setPC]
private theorem getByte_addi (s : MachineState) (rd rs : Reg) (imm : BitVec 12)
    (addr : Word) :
    (execInstrBr s (.ADDI rd rs imm)).getByte addr = s.getByte addr := by
  simp only [execInstrBr, getByte_setReg, getByte_setPC]
private theorem getByte_lbu (s : MachineState) (rd base : Reg) (addr : Word) :
    (execInstrBr s (.LBU rd base 0)).getByte addr = s.getByte addr := by
  simp only [execInstrBr, getByte_setReg, getByte_setPC]
private theorem getByte_slli (s : MachineState) (rd base : Reg) (imm : BitVec 6)
    (addr : Word) :
    (execInstrBr s (.SLLI rd base imm)).getByte addr = s.getByte addr := by
  simp only [execInstrBr, getByte_setReg, getByte_setPC]
private theorem getByte_add (s : MachineState) (rd x y : Reg) (addr : Word) :
    (execInstrBr s (.ADD rd x y)).getByte addr = s.getByte addr := by
  simp only [execInstrBr, getByte_setReg, getByte_setPC]
private theorem getByte_lw (s : MachineState) (rd base : Reg) (addr : Word) :
    (execInstrBr s (.LW rd base 0)).getByte addr = s.getByte addr := by
  simp only [execInstrBr, getByte_setReg, getByte_setPC]

theorem copyBody_preserves_byte (s : MachineState) (addr : Word)
    (hne : alignToDword addr ≠ alignToDword (s.getReg .x11)) :
    (copyBody s).getByte addr = s.getByte addr := by
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s5
    (.ADDI .x10 .x10 1)) (.ADDI .x11 .x11 4))
    (.ADDI .x18 .x18 (-1))) (.BNE .x18 .x0 (-32))).getByte _ = _
  rw [getByte_bne, getByte_addi, getByte_addi, getByte_addi]
  have hptr : s4.getReg .x11 = s.getReg .x11 := by
    simp [s1,s2,s3,s4,execInstrBr,MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  change s5.getByte addr = _
  simp only [s5, execInstrBr, hptr, getByte_setPC]
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
  simp
  rw [getByte_setWord32_ne _ _ _ _ hne]
  simp only [s4,getByte_lw,s3,getByte_add,s2,getByte_slli,s1,getByte_lbu]

private theorem erws_diff_0_1 (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 0 v) 1 = extractWord32 w 1 := by
  simp only [extractWord32, replaceWord32]
  ext i (hi : i < 32)
  simp [BitVec.truncate, BitVec.zeroExtend]
  nat_lt_cases i 32 <;> simp_all
private theorem erws_diff_1_0 (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 1 v) 0 = extractWord32 w 0 := by
  simp only [extractWord32, replaceWord32]
  ext i (hi : i < 32)
  simp [BitVec.truncate, BitVec.zeroExtend]
  nat_lt_cases i 32 <;> simp_all

theorem extractWord32_replaceWord32_other (w : Word) (v : BitVec 32)
    (writePos readPos : Fin 2) (hne : writePos ≠ readPos) :
    extractWord32 (replaceWord32 w writePos.val v) readPos.val =
      extractWord32 w readPos.val := by
  fin_cases writePos <;> fin_cases readPos <;>
    simp_all [erws_diff_0_1, erws_diff_1_0]

theorem getWord32_setWord32_other (s : MachineState) (writeAddr readAddr : Word)
    (v : BitVec 32)
    (hsep : alignToDword readAddr ≠ alignToDword writeAddr ∨
      byteOffset readAddr / 4 ≠ byteOffset writeAddr / 4) :
    (s.setWord32 writeAddr v).getWord32 readAddr = s.getWord32 readAddr := by
  simp only [getWord32_eq, setWord32_eq]
  rcases hsep with hdword | hpos
  · rw [MachineState.getMem_setMem_ne hdword]
  · by_cases halign : alignToDword readAddr = alignToDword writeAddr
    · rw [halign, MachineState.getMem_setMem_eq]
      have hwrite : byteOffset writeAddr / 4 < 2 := by
        have h := byteOffset_lt_8 (addr := writeAddr)
        omega
      have hread : byteOffset readAddr / 4 < 2 := by
        have h := byteOffset_lt_8 (addr := readAddr)
        omega
      exact extractWord32_replaceWord32_other _ _
        ⟨_, hwrite⟩ ⟨_, hread⟩ (by intro h; exact hpos (congrArg Fin.val h).symm)
    · rw [MachineState.getMem_setMem_ne halign]

theorem copyBody_preserves_word (s : MachineState) (readAddr : Word)
    (hsep : alignToDword readAddr ≠ alignToDword (s.getReg .x11) ∨
      byteOffset readAddr / 4 ≠ byteOffset (s.getReg .x11) / 4) :
    (copyBody s).getWord32 readAddr = s.getWord32 readAddr := by
  let s1 := execInstrBr s (.LBU .x19 .x10 0)
  let s2 := execInstrBr s1 (.SLLI .x20 .x19 2)
  let s3 := execInstrBr s2 (.ADD .x21 .x17 .x20)
  let s4 := execInstrBr s3 (.LW .x22 .x21 0)
  let s5 := execInstrBr s4 (.SW .x11 .x22 0)
  change (execInstrBr (execInstrBr (execInstrBr (execInstrBr s5
    (.ADDI .x10 .x10 1)) (.ADDI .x11 .x11 4))
    (.ADDI .x18 .x18 (-1))) (.BNE .x18 .x0 (-32))).getWord32 _ = _
  rw [getWord32_bne, getWord32_addi, getWord32_addi, getWord32_addi]
  have hptr : s4.getReg .x11 = s.getReg .x11 := by
    simp [s1,s2,s3,s4,execInstrBr,MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  change s5.getWord32 readAddr = _
  simp only [s5, execInstrBr, hptr, getWord32_setPC]
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
  simp
  rw [getWord32_setWord32_other _ _ _ _ hsep]
  simp only [s4,getWord32_lw,s3,getWord32_add,s2,getWord32_slli,s1,getWord32_lbu]

#print axioms copyBody_preserves_word

#print axioms copyBody_output_word
#print axioms copyBody_preserves_byte
#print axioms getWord32_setWord32_other

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67
