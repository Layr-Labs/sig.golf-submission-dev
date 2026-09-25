import SigGolfCandidate.Hypertree.SignEncodeFinish
import SigGolfCandidate.Hypertree.BalancedPatch

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Expansion
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def checksumRestInstructions : List Instr := [
  .SB .x10 .x13 0,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 1,
  .SRLI .x12 .x12 3,
  .ANDI .x13 .x12 7,
  .SB .x10 .x13 2,
  .SRLI .x12 .x12 3]

def checksumRestState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SB .x10 .x13 0)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 1)
  let s := execInstrBr s (.SRLI .x12 .x12 3)
  let s := execInstrBr s (.ANDI .x13 .x12 7)
  let s := execInstrBr s (.SB .x10 .x13 2)
  execInstrBr s (.SRLI .x12 .x12 3)

def ChecksumRestCode (image : Image) (pc : Word) : Prop :=
  ∀ (s : MachineState) (i : Fin 8), s.pc = pc + BitVec.ofNat 64 (4*i.val) →
    fetch image s = some (.base (checksumRestInstructions[i.val]'(by simp [checksumRestInstructions])))

theorem checksumRest_block (image : Image) (base : Word) (code : ChecksumRestCode image base)
    (s : MachineState) (pc : s.pc = base) (ptr : s.getReg .x10 = 0x8062b) :
    OrdinarySteps image s 8 (checksumRestState s) := by
  let s1 := execInstrBr s (.SB .x10 .x13 0)
  let s2 := execInstrBr s1 (.SRLI .x12 .x12 3)
  let s3 := execInstrBr s2 (.ANDI .x13 .x12 7)
  let s4 := execInstrBr s3 (.SB .x10 .x13 1)
  let s5 := execInstrBr s4 (.SRLI .x12 .x12 3)
  let s6 := execInstrBr s5 (.ANDI .x13 .x12 7)
  let s7 := execInstrBr s6 (.SB .x10 .x13 2)
  let s8 := execInstrBr s7 (.SRLI .x12 .x12 3)
  apply OrdinarySteps.step s s1 _ (.base (.SB .x10 .x13 0)) 7
  · apply code _ 0
    simp [execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s1 s2 _ (.base (.SRLI .x12 .x12 3)) 6
  · apply code _ 1
    simp [s1, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ANDI .x13 .x12 7)) 5
  · apply code _ 2
    simp [s1, s2, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SB .x10 .x13 1)) 4
  · apply code _ 3
    simp [s1, s2, s3, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, ptr,
      accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x12 .x12 3)) 3
  · apply code _ 4
    simp [s1, s2, s3, s4, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ANDI .x13 .x12 7)) 2
  · apply code _ 5
    simp [s1, s2, s3, s4, s5, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SB .x10 .x13 2)) 1
  · apply code _ 6
    simp [s1, s2, s3, s4, s5, s6, execInstrBr, pc, BitVec.add_assoc]
  · simp [s1, s2, s3, s4, s5, s6, s7, ordinaryStep, memoryArgumentsValid, execInstrBr,
      signExtend12, ptr, accessValid, rangeValid, MEMORY_BYTES,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.SRLI .x12 .x12 3)) 0
  · apply code _ 7
    simp [s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, BitVec.add_assoc]
  · rfl
  exact OrdinarySteps.refl _

theorem checksumState_rest (s : MachineState) :
    checksumRestState (execInstrBr s (.ANDI .x13 .x12 7)) = checksumState s := by
  rfl

theorem checksumRestState_pc (s : MachineState) :
    (checksumRestState s).pc = s.pc + 32 := by
  simp [checksumRestState, execInstrBr, BitVec.add_assoc]

theorem checksumRestState_sp (s : MachineState) :
    (checksumRestState s).getReg .x2 = s.getReg .x2 := by
  simp [checksumRestState, execInstrBr, MachineState.getReg_setReg_ne]

theorem checksumRestState_byte (s : MachineState) (a : Word) :
    (checksumRestState s).getByte a =
      if a = s.getReg .x10 + 2 then ((s.getReg .x12 >>> 6) &&& 7).truncate 8 else
      if a = s.getReg .x10 + 1 then ((s.getReg .x12 >>> 3) &&& 7).truncate 8 else
      if a = s.getReg .x10 then (s.getReg .x13).truncate 8 else s.getByte a := by
  simp [checksumRestState, execInstrBr, signExtend12, getByte_setByte,
    Memory.getByte_setReg, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, ← BitVec.shiftRight_add]

theorem checksumRestState_output (s : MachineState) (checksum : Nat)
    (bound : checksum ≤ 301) (ptr : s.getReg .x10 = 0x8062b)
    (value : s.getReg .x12 = BitVec.ofNat 64 checksum)
    (low : s.getReg .x13 = s.getReg .x12 &&& 7) (i : Fin 3) :
    (checksumRestState s).getByte (BitVec.ofNat 64 (0x8062b + i.val)) =
      BitVec.ofNat 8 (checksum / 8 ^ i.val % 8) := by
  fin_cases i
  · simpa [checksumRestState_byte, ptr, value, low] using checksum_digit checksum bound 0
  · simpa [checksumRestState_byte, ptr, value, low] using checksum_digit checksum bound 1
  · simpa [checksumRestState_byte, ptr, value, low] using checksum_digit checksum bound 2

theorem checksumRestState_frame (s : MachineState) (ptr : s.getReg .x10 = 0x8062b)
    (a : Word) (outside : ∀ i : Fin 3, a ≠ BitVec.ofNat 64 (0x8062b + i.val)) :
    (checksumRestState s).getByte a = s.getByte a := by
  have h0 : a ≠ 0x8062b := outside 0
  have h1 : a ≠ 0x8062c := outside 1
  have h2 : a ≠ 0x8062d := outside 2
  rw [checksumRestState_byte, ptr]
  change (if a = 0x8062d then _ else if a = 0x8062c then _ else
    if a = 0x8062b then _ else _) = _
  rw [if_neg h2, if_neg h1, if_neg h0]

theorem checksumRestState_refines (s : MachineState) (message : Reference.Digest)
    (ptr : s.getReg .x10 = 0x8062b)
    (value : s.getReg .x12 = BitVec.ofNat 64 (Reference.checksum message))
    (low : s.getReg .x13 = s.getReg .x12 &&& 7)
    (digits : ∀ i : Fin 43, s.getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
      BitVec.ofNat 8 (Reference.payloadDigit message i)) :
    ∀ i : Reference.Chain,
      (checksumRestState s).getByte (BitVec.ofNat 64 (0x80600 + i.val)) =
        BitVec.ofNat 8 (Reference.digit message i).val := by
  intro i
  by_cases small : i.val < 43
  · rw [checksumRestState_frame s ptr, digits ⟨i.val, small⟩]
    · have rawLt : Reference.messageDigit message ⟨i.val, small⟩ < 8 := by
        unfold Reference.messageDigit
        exact Nat.mod_lt _ (by decide)
      have payloadLt : Reference.payloadDigit message ⟨i.val, small⟩ < 8 := by
        unfold Reference.payloadDigit
        split_ifs <;> omega
      simpa [Reference.digit, small, Nat.mod_eq_of_lt small,
        Nat.mod_eq_of_lt payloadLt]
    · intro j
      have hj := j.isLt
      have eq : 0x8062b + j.val = 0x80600 + (43 + j.val) := by omega
      rw [eq]
      exact digit_address_ne i.val (43 + j.val) i.isLt (by omega) (by omega)
  · have hj : i.val - 43 < 3 := by have := i.isLt; omega
    have bound : Reference.checksum message ≤ 301 := Nat.sub_le _ _
    have output := checksumRestState_output s (Reference.checksum message) bound ptr value low
      ⟨i.val - 43, hj⟩
    have addr : 0x8062b + (i.val - 43) = 0x80600 + i.val := by omega
    simpa [addr, Reference.digit, small] using output

end SigGolfCandidate.Hypertree.Signing
#print axioms SigGolfCandidate.Hypertree.Signing.checksumRest_block
#print axioms SigGolfCandidate.Hypertree.Signing.checksumRestState_output
#print axioms SigGolfCandidate.Hypertree.Signing.checksumRestState_frame
