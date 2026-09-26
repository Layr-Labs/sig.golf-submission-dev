import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2CaptureAny67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSafety67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Round67. -/
section
/-! The selected upper WOTS witness lies in the signature buffer, while the
digit table and both witness stores are within the machine's address space. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSafety67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev selector := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigitAfter67.digitState
private abbrev pointer := GroupedBalancedSignUpperCaptureWriteAfter67.pointer

theorem pointer_nat (s : MachineState) (witnessBase chain : Nat)
    (witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (chainBound : chain < 67)
    (witnessBound : witnessBase + 16*chain + 16 ≤ 0x80000) :
    (pointer (digit (selector s))).toNat = witnessBase + 16*chain := by
  calc
    (pointer (digit (selector s))).toNat =
        (s.getMem 0x810f0 + (s.getMem 0x81030 <<< 4)).toNat :=
      congrArg BitVec.toNat
        (GroupedBalancedSignUpperH2CaptureAny67.capture_pointer s)
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

#print axioms pointer_nat
#print axioms safe
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSafety67

end

/-! One complete H2 round: update step header, hash, capture the selected
prefix value if needed, and branch to the next round or endpoint store. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Round67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev advanced := GroupedBalancedSignUpperH2Tick67.advanced
private abbrev pointer := GroupedBalancedSignUpperCaptureWriteAfter67.pointer
private abbrev selector := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigitAfter67.digitState

noncomputable def roundResult (hash : Hash) (s : MachineState) : MachineState :=
  GroupedBalancedSignUpperH2CaptureAny67.captureResult (advanced hash s)

theorem round_stack (hash : Hash) (s : MachineState) :
    (roundResult hash s).getReg .x2 = s.getReg .x2 := by
  rw [roundResult,GroupedBalancedSignUpperH2CaptureAny67.capture_stack,
    GroupedBalancedSignUpperH2Tick67.advanced_stack]

theorem safe_after_hash (hash : Hash) (s : MachineState)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (witnessBase chain : Nat)
    (witness : s.getMem 0x810f0 = BitVec.ofNat 64 witnessBase)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (chainBound : chain < 67)
    (witnessBound : witnessBase + 16*chain + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0) :
    accessValid (0x80600 + (advanced hash s).getMem 0x81030) 1 = true ∧
    accessValid (pointer (digit (selector (advanced hash s)))) 8 = true ∧
    accessValid (pointer (digit (selector (advanced hash s))) + 8) 8 = true ∧
    (pointer (digit (selector (advanced hash s)))).toNat < 0x80000 ∧
    (pointer (digit (selector (advanced hash s))) + 8).toNat < 0x80000 := by
  have counterFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s source destination 0x81030
    (by decide) (by intro i; fin_cases i <;> decide)
  have witnessFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
    hash s source destination 0x810f0
    (by decide) (by intro i; fin_cases i <;> decide)
  exact GroupedBalancedSignUpperCaptureSafety67.safe
    (advanced hash s) witnessBase chain
    (witnessFrame.trans witness) (counterFrame.trans counter)
    chainBound witnessBound aligned

theorem round_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1a38)
    (service : s.getReg .x5 = 1)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (safeDigit : accessValid
      (0x80600 + (advanced hash s).getMem 0x81030) 1 = true)
    (safeWitness : accessValid
      (pointer (digit (selector (advanced hash s)))) 8 = true)
    (safeWitnessNext : accessValid
      (pointer (digit (selector (advanced hash s))) + 8) 8 = true)
    (low0 : (pointer (digit (selector (advanced hash s)))).toNat < 0x80000)
    (low1 : (pointer (digit (selector (advanced hash s))) + 8).toNat < 0x80000) :
    ∃ n, n ≤ 30 ∧
      Trace hash image s n (n+7) 1 1 (roundResult hash s) ∧
      (roundResult hash s).pc =
        (if s.getReg .x21 + 1 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
      (roundResult hash s).getReg .x21 = s.getReg .x21 + 1 ∧
      (roundResult hash s).getReg .x20 = s.getReg .x20 ∧
      (roundResult hash s).getReg .x19 = s.getReg .x19 ∧
      (roundResult hash s).getReg .x5 = s.getReg .x5 ∧
      (roundResult hash s).getReg .x10 = s.getReg .x10 ∧
      (roundResult hash s).getReg .x11 = s.getReg .x11 ∧
      (roundResult hash s).getReg .x12 = s.getReg .x12 ∧
      (∀ a : Word, 0x80600 ≤ a.toNat →
        (roundResult hash s).getMem a = s.getMem a) := by
  have first := GroupedBalancedSignUpperH2Tick67.tick_trace hash s pc
    service source bits destination
  have apc := GroupedBalancedSignUpperH2Tick67.advanced_pc hash s pc
  obtain ⟨m,second,secondTrace,mBound,secondPC,secondFrame,finalEq⟩ :=
    GroupedBalancedSignUpperH2CaptureAny67.capture_any
      (advanced hash s) apc safeDigit safeWitness safeWitnessNext low0 low1
  have regA := GroupedBalancedSignUpperH2Tick67.advanced_regs hash s
  have regC := GroupedBalancedSignUpperH2CaptureAny67.capture_regs (advanced hash s)
  have regF :
      (roundResult hash s).getReg .x21 = s.getReg .x21 + 1 ∧
      (roundResult hash s).getReg .x20 = s.getReg .x20 ∧
      (roundResult hash s).getReg .x19 = s.getReg .x19 ∧
      (roundResult hash s).getReg .x5 = s.getReg .x5 ∧
      (roundResult hash s).getReg .x10 = s.getReg .x10 ∧
      (roundResult hash s).getReg .x11 = s.getReg .x11 ∧
      (roundResult hash s).getReg .x12 = s.getReg .x12 := by
    exact ⟨(regC.2.2.2.2.2.2).trans regA.1,
      (regC.2.2.2.2.2.1).trans regA.2.1,
      (regC.2.2.2.2.1).trans regA.2.2.1,
      regC.1.trans regA.2.2.2.1,
      regC.2.1.trans regA.2.2.2.2.1,
      regC.2.2.1.trans regA.2.2.2.2.2.1,
      regC.2.2.2.1.trans regA.2.2.2.2.2.2⟩
  refine ⟨3+m,by omega,?_,?_,regF.1,regF.2.1,
    regF.2.2.1,regF.2.2.2.1,regF.2.2.2.2.1,
    regF.2.2.2.2.2.1,regF.2.2.2.2.2.2,?_⟩
  · have full := first.trans (secondTrace.trace (hash := hash))
    rw [finalEq] at full
    have same : Trace hash image s (3+m) (10+m) 1 1
        (roundResult hash s) := by simpa only [roundResult] using full
    have count : 10+m = (3+m)+7 := by omega
    simpa only [count] using same
  · rw [finalEq] at secondPC
    change (GroupedBalancedSignUpperH2CaptureAny67.captureResult
      (advanced hash s)).pc = _
    rw [secondPC,regA.1,regA.2.1]
  · intro a high
    have firstFrame := GroupedBalancedSignUpperH2Tick67.advanced_frame
      hash s source destination a
      (by intro eq; have hn := congrArg BitVec.toNat eq;
          simp at hn; omega)
      (by intro i eq; have hn := congrArg BitVec.toNat eq;
          fin_cases i <;> simp [Signing.wordAddress] at hn <;> omega)
    have secondHigh : 0x80000 ≤ a.toNat := by omega
    rw [finalEq] at secondFrame
    exact (secondFrame a secondHigh).trans firstFrame

theorem round_header (hash : Hash) (s : MachineState)
    (base chain old step : Nat)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (stepReg : s.getReg .x21 = BitVec.ofNat 64 step)
    (header : s.getMem 0x80000 = KeygenDomain.header 2 base 0 chain old)
    (baseBound : base < 256) (chainBound : chain < 256)
    (oldBound : old < 256) (stepBound : step < 256)
    (low0 : (pointer (digit (selector (advanced hash s)))).toNat < 0x80000)
    (low1 : (pointer (digit (selector (advanced hash s))) + 8).toNat < 0x80000) :
    (roundResult hash s).getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain step := by
  rw [roundResult,
    GroupedBalancedSignUpperH2CaptureAny67.capture_high_frame
      (advanced hash s) 0x80000 (by decide) low0 low1]
  exact GroupedBalancedSignUpperH2Tick67.advanced_header hash s
    base chain old step source destination stepReg header
    baseBound chainBound oldBound stepBound

theorem round_index (hash : Hash) (s : MachineState)
    (source : s.getReg .x10 = 0x80000)
    (destination : s.getReg .x12 = 0x80020)
    (low0 : (pointer (digit (selector (advanced hash s)))).toNat < 0x80000)
    (low1 : (pointer (digit (selector (advanced hash s))) + 8).toNat < 0x80000) :
    ∀ i : Fin 3,
      (roundResult hash s).getMem (Signing.wordAddress 0x80008 i.val) =
        s.getMem (Signing.wordAddress 0x80008 i.val) := by
  intro i
  have hi : 0x80000 ≤ (Signing.wordAddress 0x80008 i.val).toNat := by
    fin_cases i <;> decide
  rw [roundResult,
    GroupedBalancedSignUpperH2CaptureAny67.capture_high_frame
      (advanced hash s) _ hi low0 low1]
  exact GroupedBalancedSignUpperH2Tick67.advanced_frame hash s
    source destination _
    (by fin_cases i <;> decide)
    (by intro j; fin_cases i <;> fin_cases j <;> decide)

theorem round_chain_words (hash : Hash) (s : MachineState)
    (base leaf step : Nat) (chain : GroupedBalancedUpperTree67.ChainMixed)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (destination : s.getReg .x12 = 0x80020)
    (header : replaceByte (s.getMem 0x80000) 4
      ((s.getReg .x21).truncate 8) =
        KeygenDomain.header 2 base 0 chain.val step)
    (tree : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (value : Reference.Digest)
    (words : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64)
    (low0 : (pointer (digit (selector (advanced hash s)))).toNat < 0x80000)
    (low1 : (pointer (digit (selector (advanced hash s))) + 8).toNat < 0x80000) :
    ∀ i : Fin 2,
      (roundResult hash s).getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.chainHash hash base leaf
          chain step value).extractLsb' (64*i.val) 64 := by
  intro i
  have hi : 0x80000 ≤ (Signing.wordAddress 0x80020 i.val).toNat := by
    fin_cases i <;> decide
  rw [roundResult,
    GroupedBalancedSignUpperH2CaptureAny67.capture_high_frame
      (advanced hash s) _ hi low0 low1]
  exact GroupedBalancedSignUpperH2Tick67.advanced_chain_words hash s
    base leaf step chain source bits destination header tree value words i

#print axioms round_trace
#print axioms round_header
#print axioms round_chain_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Round67
