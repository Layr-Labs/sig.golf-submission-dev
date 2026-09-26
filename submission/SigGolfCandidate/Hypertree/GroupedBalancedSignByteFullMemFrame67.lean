import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteCopyMem67

/-! Memory outside the byte decoder's output buffer is unchanged. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullMemFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open GroupedBalancedDecoderByteLoop67
open GroupedBalancedDecoderByteSumLoop67
open GroupedBalancedSignByteSetup67
open GroupedBalancedSignByteCopy67
open GroupedBalancedSignByteCopyLoop67
open GroupedBalancedSignByteCopyMem67
open GroupedBalancedSignByteBranch67
open GroupedBalancedSignByteCompose67
open GroupedBalancedSignByteTail67
open GroupedBalancedSignByteFull67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState, execInstrBr]

theorem sumBody_mem (s : MachineState) (a : Word) :
    (sumBody s).getMem a = s.getMem a := by
  simp [sumBody, execInstrBr]

theorem sumLoop_mem (s : MachineState) (n : Nat) (a : Word) :
    (sumLoop s n).getMem a = s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [sumLoop, sumBody_mem] using ih

theorem copyBody_mem (s : MachineState) (a : Word)
    (hne : a ≠ alignToDword (s.getReg .x11)) :
    (copyBody s).getMem a = s.getMem a := by
  simp [copyBody, execInstrBr, setWord32_eq, MachineState.getMem_setMem_ne,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12,
    hne]

theorem copyLoop_mem (s : MachineState) (a : Word) (n : Nat)
    (output : s.getReg .x11 = 0x80600)
    (hne : ∀ k, k < n → a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k))) :
    (copyLoop s n).getMem a = s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hptr : (copyLoop s n).getReg .x11 =
        BitVec.ofNat 64 (0x80600+4*n) := by
      rw [copyLoop_output_pointer, output, BitVec.ofNat_add]
      rfl
    change (copyBody (copyLoop s n)).getMem a = _
    rw [copyBody_mem _ _ (by rw [hptr]; exact hne n (by omega))]
    exact ih (by intro k hk; exact hne k (by omega))

theorem smallBranch_mem (s : MachineState) (a : Word)
    (hne : a ≠ alignToDword (s.getReg .x11 + 64)) :
    (smallBranch s).getMem a = s.getMem a := by
  simp [smallBranch, commonBranch, branchPrefix, execInstrBr, setByte_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  intro h
  exact False.elim (hne h)

theorem largeBranch_mem (s : MachineState) (a : Word)
    (hne : a ≠ alignToDword (s.getReg .x11 + 64)) :
    (largeBranch s).getMem a = s.getMem a := by
  simp [largeBranch, commonBranch, branchPrefix, execInstrBr, setByte_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  intro h
  exact False.elim (hne h)

theorem selectedBranch_mem (s : MachineState) (message : BitVec 128)
    (a : Word) (hne : a ≠ alignToDword (s.getReg .x11 + 64)) :
    (selectedBranch s message).getMem a = s.getMem a := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simpa [selectedBranch, h] using smallBranch_mem s a hne
  · simpa [selectedBranch, h] using largeBranch_mem s a hne

theorem tail_mem (s : MachineState) (a : Word)
    (h1 : a ≠ alignToDword (s.getReg .x11 + 1))
    (h2 : a ≠ alignToDword (s.getReg .x11 + 2)) :
    (tailState s).getMem a = s.getMem a := by
  simp [tailState, execInstrBr, setByte_eq,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    signExtend12]
  split_ifs <;> simp_all

theorem selectedBranch_x11 (s : MachineState) (message : BitVec 128) :
    (selectedBranch s message).getReg .x11 = s.getReg .x11 := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simp [selectedBranch, h, smallBranch, commonBranch, branchPrefix,
      execInstrBr, MachineState.setByte, MachineState.getReg_setReg_ne]
  · simp [selectedBranch, h, largeBranch, commonBranch, branchPrefix,
      execInstrBr, MachineState.setByte, MachineState.getReg_setReg_ne]

theorem postSum_mem (s : MachineState) (message : BitVec 128)
    (a : Word) (output : s.getReg .x11 = 0x80600)
    (hflag : a ≠ (0x80640 : Word))
    (hcopy : ∀ k, k < 16 →
      a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k))) :
    (postSumState s message).getMem a = s.getMem a := by
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hb11 : b.getReg .x11 = 0x80600 := by
    rw [selectedBranch_x11, output]
  have hc11 : c.getReg .x11 = 0x80640 := by
    rw [copyLoop_output_pointer, hb11]
    decide
  have flag1 : a ≠ alignToDword (c.getReg .x11 + 1) := by
    rw [hc11]
    change a ≠ alignToDword (0x80641 : Word)
    convert hflag using 1
    decide
  have flag2 : a ≠ alignToDword (c.getReg .x11 + 2) := by
    rw [hc11]
    change a ≠ alignToDword (0x80642 : Word)
    convert hflag using 1
    decide
  have branchFlag : a ≠ alignToDword (s.getReg .x11 + 64) := by
    rw [output]
    change a ≠ alignToDword (0x80640 : Word)
    convert hflag using 1
    decide
  change (tailState c).getMem a = _
  rw [tail_mem c a flag1 flag2,
    copyLoop_mem b a 16 hb11 hcopy,
    selectedBranch_mem s message a branchFlag]

theorem fullDecoder_mem (s : MachineState) (message : BitVec 128)
    (a : Word)
    (hflag : a ≠ (0x80640 : Word))
    (hcopy : ∀ k, k < 16 →
      a ≠ alignToDword (BitVec.ofNat 64 (0x80600+4*k))) :
    (fullDecoderState s message).getMem a = s.getMem a := by
  let p := setupState s
  let q := sumLoop p 16
  have hsetup : p.getReg .x11 = 0x80600 := by
    simp [p, setupState, execInstrBr, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, signExtend12]
  have hq11 : q.getReg .x11 = 0x80600 := by
    rw [GroupedBalancedSignByteFull67.sumLoop_x11, hsetup]
  change (postSumState q message).getMem a = _
  rw [postSum_mem q message a hq11 hflag hcopy,
    sumLoop_mem p 16 a, setup_mem s a]

theorem copyBody_x2 (s : MachineState) :
    (copyBody s).getReg .x2 = s.getReg .x2 := by
  have getReg_setWord32 (t : MachineState) (addr : Word) (v : BitVec 32) :
      (t.setWord32 addr v).getReg .x2 = t.getReg .x2 := by
    simp [MachineState.setWord32, MachineState.setMem]
    rfl
  simp [copyBody, execInstrBr, getReg_setWord32,
    MachineState.getReg_setReg_ne, signExtend12]

theorem copyLoop_x2 (s : MachineState) (n : Nat) :
    (copyLoop s n).getReg .x2 = s.getReg .x2 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copyLoop, copyBody_x2] using ih

theorem selectedBranch_x2 (s : MachineState) (message : BitVec 128) :
    (selectedBranch s message).getReg .x2 = s.getReg .x2 := by
  by_cases h : GroupedBalancedQuaternary.rawSum message < 96
  · simp [selectedBranch, h, smallBranch, commonBranch, branchPrefix,
      execInstrBr, MachineState.setByte, MachineState.getReg_setReg_ne]
  · simp [selectedBranch, h, largeBranch, commonBranch, branchPrefix,
      execInstrBr, MachineState.setByte, MachineState.getReg_setReg_ne]

theorem tail_x2 (s : MachineState) :
    (tailState s).getReg .x2 = s.getReg .x2 := by
  simp [tailState, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_ne]

theorem fullDecoder_x2 (s : MachineState) (message : BitVec 128) :
    (fullDecoderState s message).getReg .x2 = s.getReg .x2 := by
  let p := setupState s
  let q := sumLoop p 16
  let b := selectedBranch q message
  let c := copyLoop b 16
  change (tailState c).getReg .x2 = _
  rw [tail_x2, copyLoop_x2, selectedBranch_x2,
    GroupedBalancedSignByteFull67.sumLoop_x2]
  simp [p, setupState, execInstrBr, MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullMemFrame67
