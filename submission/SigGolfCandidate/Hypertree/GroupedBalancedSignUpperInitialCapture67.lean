import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2RunFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureCompose67

/-! Selected-prefix capture before the first H2 call of one upper WOTS chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperInitialCapture67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev selector := GroupedBalancedSignUpperCaptureSelector67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigit67.digitState
private abbrev write := GroupedBalancedSignUpperCaptureWrite67.writeState
private abbrev pointer := GroupedBalancedSignUpperCaptureWrite67.pointer

noncomputable def captureResult (s : MachineState) : MachineState := by
  classical
  exact if s.getMem 0x810e0 = s.getMem 0x810e8 then
    if GroupedBalancedSignUpperCaptureCompose67.DigitMatches s then
      write (digit (selector s))
    else digit (selector s)
  else selector s

theorem capture_pointer (s : MachineState) :
    pointer (digit (selector s)) =
      s.getMem 0x810f0 + (s.getMem 0x81030 <<< 4) := by
  simp [pointer,GroupedBalancedSignUpperCaptureWrite67.pointer,
    digit,GroupedBalancedSignUpperCaptureDigit67.digitState,
    selector,GroupedBalancedSignUpperCaptureSelector67.selectorState,
    execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12]

theorem pointer_nat (s : MachineState) (witnessBase chain : Nat)
    (witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (chainBound : chain < 67)
    (witnessBound : witnessBase + 16*chain + 16 ≤ 0x80000) :
    (pointer (digit (selector s))).toNat = witnessBase + 16*chain := by
  calc
    (pointer (digit (selector s))).toNat =
        (s.getMem 0x810f0 + (s.getMem 0x81030 <<< 4)).toNat :=
      congrArg BitVec.toNat (capture_pointer s)
    _ = witnessBase + 16*chain := by
      rw [witness,counter,BitVec.toNat_add,BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq,BitVec.toNat_ofNat]
      simp only [show (2:Nat)^4 = 16 by decide,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : chain < 2^64),
        Nat.mod_eq_of_lt (by omega : witnessBase < 2^64),
        Nat.mod_eq_of_lt (by omega : chain*16 < 2^64),
        Nat.mod_eq_of_lt (by omega : witnessBase + chain*16 < 2^64)]
      omega

theorem safe (s : MachineState) (witnessBase chain : Nat)
    (witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (chainBound : chain < 67)
    (witnessBound : witnessBase + 16*chain + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    accessValid (0x80600 + s.getMem 0x81030) 1 = true ∧
    accessValid (pointer (digit (selector s))) 8 = true ∧
    accessValid (pointer (digit (selector s)) + 8) 8 = true ∧
    (pointer (digit (selector s))).toNat < 0x80000 ∧
    (pointer (digit (selector s)) + 8).toNat < 0x80000 := by
  have ptr := pointer_nat s witnessBase chain witness counter chainBound witnessBound
  have ptrNext : (pointer (digit (selector s)) + 8).toNat =
      witnessBase + 16*chain + 8 := by
    rw [BitVec.toNat_add,ptr]
    change (witnessBase+16*chain+8) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*chain+8 < 2^64)]
  have digitAddr : (0x80600 + s.getMem 0x81030).toNat = 0x80600+chain := by
    rw [counter,BitVec.toNat_add,BitVec.toNat_ofNat]
    change (0x80600 + chain % 2^64) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega : chain < 2^64),
      Nat.mod_eq_of_lt (by omega : 0x80600+chain < 2^64)]
  refine ⟨?_,?_,?_,by rw [ptr]; omega,by rw [ptrNext]; omega⟩
  · simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
    rw [digitAddr]
    simp only [MEMORY_BYTES]
    constructor <;> omega
  · simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
    rw [ptr]
    simp only [MEMORY_BYTES]
    constructor <;> omega
  · simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
    rw [ptrNext]
    simp only [MEMORY_BYTES]
    constructor <;> omega

theorem capture_any (s : MachineState) (pc : s.pc = 0x19d0)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true)
    (safeWitness : accessValid (pointer (digit (selector s))) 8 = true)
    (safeWitnessNext : accessValid (pointer (digit (selector s)) + 8) 8 = true)
    (low0 : (pointer (digit (selector s))).toNat < 0x80000)
    (low1 : (pointer (digit (selector s)) + 8).toNat < 0x80000) :
    ∃ (n : Nat) (final : MachineState),
      OrdinarySteps image s n final ∧ n ≤ 26 ∧
      final.pc = 0x1a38 ∧
      (∀ a : Word, 0x80000 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      final = captureResult s := by
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · by_cases matched : GroupedBalancedSignUpperCaptureCompose67.DigitMatches s
    · obtain ⟨path,pcFinal,w0,w1⟩ :=
        GroupedBalancedSignUpperCaptureCompose67.selected_matched s pc
          selected matched safeDigit safeWitness safeWitnessNext
      refine ⟨26,_,path,by decide,pcFinal,?_,?_⟩
      · intro a high
        exact GroupedBalancedSignUpperCaptureCompose67.matched_high_frame
          s a high low0 low1
      · change s.getMem 528608#64 = s.getMem 528616#64 at selected
        simp [captureResult,selected,matched]
    · obtain ⟨path,pcFinal,frame⟩ :=
        GroupedBalancedSignUpperCaptureCompose67.selected_unmatched s pc
          selected matched safeDigit
      refine ⟨15,_,path,by decide,pcFinal,fun a _ => frame a,?_⟩
      change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [captureResult,selected,matched]
  · obtain ⟨path,pcFinal,frame⟩ :=
      GroupedBalancedSignUpperCaptureCompose67.unselected s pc selected
    refine ⟨7,_,path,by decide,pcFinal,fun a _ => frame a,?_⟩
    change s.getMem 528608#64 ≠ s.getMem 528616#64 at selected
    simp [captureResult,selected]

theorem capture_stack (s : MachineState) :
    (captureResult s).getReg .x2 = s.getReg .x2 := by
  classical
  unfold captureResult
  split_ifs <;>
    simp [selector,digit,write,
      GroupedBalancedSignUpperCaptureSelector67.selectorState,
      GroupedBalancedSignUpperCaptureDigit67.digitState,
      GroupedBalancedSignUpperCaptureWrite67.writeState,
      execInstrBr,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem capture_regs (s : MachineState) :
    (captureResult s).getReg .x5 = s.getReg .x5 ∧
    (captureResult s).getReg .x10 = s.getReg .x10 ∧
    (captureResult s).getReg .x11 = s.getReg .x11 ∧
    (captureResult s).getReg .x12 = s.getReg .x12 ∧
    (captureResult s).getReg .x19 = s.getReg .x19 ∧
    (captureResult s).getReg .x20 = s.getReg .x20 ∧
    (captureResult s).getReg .x21 = s.getReg .x21 := by
  classical
  unfold captureResult
  split_ifs <;>
    simp [selector,digit,write,
      GroupedBalancedSignUpperCaptureSelector67.selectorState,
      GroupedBalancedSignUpperCaptureDigit67.digitState,
      GroupedBalancedSignUpperCaptureWrite67.writeState,
      execInstrBr,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

#print axioms capture_any
#print axioms capture_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperInitialCapture67
