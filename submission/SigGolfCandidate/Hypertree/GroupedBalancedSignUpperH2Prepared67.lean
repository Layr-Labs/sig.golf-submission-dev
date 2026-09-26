import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMaxCommon67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMax6567
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMax6667
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Ready67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMaxChoice67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Prepared67. -/
section
/-! All three WOTS chain lengths reach the same H2 setup point. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMaxChoice67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def maxFor (chain : Word) : Word :=
  if chain = (65#64) then 8 else if chain = (66#64) then 10 else 3

def stepsFor (chain : Word) : Nat :=
  if chain = (65#64) then 7 else 8

theorem choose (s : MachineState) (pc : s.pc = 0x198c) :
    ∃ final, OrdinarySteps image s (stepsFor (s.getReg .x19)) final ∧
      final.pc = 0x19b8 ∧
      final.getReg .x20 = maxFor (s.getReg .x19) ∧
      final.getReg .x21 = 0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, final.getMem a = s.getMem a) := by
  by_cases h65 : s.getReg .x19 = 65
  · let final := GroupedBalancedSignUpperMax6567.maxState s
    have h65bv : s.getReg .x19 = (65#64) := by
      simpa only [show (65 : Word) = (65#64) by decide] using h65
    obtain ⟨hm,hs,hc⟩ := GroupedBalancedSignUpperMax6567.max_data s
    refine ⟨final,?_,GroupedBalancedSignUpperMax6567.max_pc s pc h65,?_,hs,hc,?_,?_⟩
    · simpa [stepsFor,h65bv] using GroupedBalancedSignUpperMax6567.max_steps s pc h65
    · simpa [maxFor,h65bv] using hm
    · simp [final,GroupedBalancedSignUpperMax6567.maxState,execInstrBr,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    · exact GroupedBalancedSignUpperMax6567.max_frame s
  · by_cases h66 : s.getReg .x19 = 66
    · let final := GroupedBalancedSignUpperMax6667.maxState s
      have h65bv : s.getReg .x19 ≠ (65#64) := by
        simpa only [show (65 : Word) = (65#64) by decide] using h65
      have h66bv : s.getReg .x19 = (66#64) := by
        simpa only [show (66 : Word) = (66#64) by decide] using h66
      obtain ⟨hm,hs,hc⟩ := GroupedBalancedSignUpperMax6667.max_data s
      refine ⟨final,?_,GroupedBalancedSignUpperMax6667.max_pc s pc h65 h66,?_,hs,hc,?_,?_⟩
      · simpa [stepsFor,h65bv] using
          GroupedBalancedSignUpperMax6667.max_steps s pc h65 h66
      · simpa [maxFor,h65bv,h66bv] using hm
      · simp [final,GroupedBalancedSignUpperMax6667.maxState,execInstrBr,
          MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
      · exact GroupedBalancedSignUpperMax6667.max_frame s
    · let final := GroupedBalancedSignUpperMaxCommon67.maxState s
      have h65bv : s.getReg .x19 ≠ (65#64) := by
        simpa only [show (65 : Word) = (65#64) by decide] using h65
      have h66bv : s.getReg .x19 ≠ (66#64) := by
        simpa only [show (66 : Word) = (66#64) by decide] using h66
      obtain ⟨hm,hs,hc⟩ := GroupedBalancedSignUpperMaxCommon67.max_data s
      refine ⟨final,?_,GroupedBalancedSignUpperMaxCommon67.max_pc s pc h65 h66,?_,hs,hc,?_,?_⟩
      · simpa [stepsFor,h65bv] using
          GroupedBalancedSignUpperMaxCommon67.max_steps s pc h65 h66
      · simpa [maxFor,h65bv,h66bv] using hm
      · simp [final,GroupedBalancedSignUpperMaxCommon67.maxState,execInstrBr,
          MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
      · exact GroupedBalancedSignUpperMaxCommon67.max_frame s

theorem max_for_chain (chain : Fin 67) :
    maxFor (BitVec.ofNat 64 chain.val) =
      BitVec.ofNat 64 (GroupedBalancedChecksum67.maxDigit chain) := by
  fin_cases chain <;> decide

#print axioms choose
#print axioms max_for_chain
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMaxChoice67

end

/-! The first H2 query layout and maximum chain length after seed selection. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Prepared67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev layout := GroupedBalancedSignUpperH2Layout67.prepared
private abbrev maxFor := GroupedBalancedSignUpperMaxChoice67.maxFor
private abbrev stepsFor := GroupedBalancedSignUpperMaxChoice67.stepsFor

theorem prepare (s : MachineState) (pc : s.pc = 0x18e8) :
    ∃ final,
      OrdinarySteps image s (47 + stepsFor (s.getReg .x19)) final ∧
      final.pc = 0x19d0 ∧
      final.getReg .x20 = maxFor (s.getReg .x19) ∧
      final.getReg .x21 = 0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x10 = 0x80000 ∧
      final.getReg .x11 = 384 ∧
      final.getReg .x12 = 0x80020 ∧
      final.getReg .x5 = 1 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, final.getMem a = (layout s).getMem a) := by
  have ltrace := GroupedBalancedSignUpperH2Layout67.prepared_steps s pc
  have lpc := GroupedBalancedSignUpperH2Layout67.prepared_pc s pc
  obtain ⟨m,choose,mpc,max,step,chain,stack,mframe⟩ :=
    GroupedBalancedSignUpperMaxChoice67.choose (layout s) lpc
  let final := GroupedBalancedSignUpperH2Ready67.readyState m
  have rtrace := GroupedBalancedSignUpperH2Ready67.ready_steps m mpc
  have rpc := GroupedBalancedSignUpperH2Ready67.ready_pc m mpc
  obtain ⟨source,bits,destination,service⟩ :=
    GroupedBalancedSignUpperH2Ready67.ready_regs m
  have x20 : final.getReg .x20 = m.getReg .x20 := by
    simp [final,GroupedBalancedSignUpperH2Ready67.readyState,execInstrBr,
      MachineState.getReg_setReg_ne]
  have x21 : final.getReg .x21 = m.getReg .x21 := by
    simp [final,GroupedBalancedSignUpperH2Ready67.readyState,execInstrBr,
      MachineState.getReg_setReg_ne]
  have x19 : final.getReg .x19 = m.getReg .x19 := by
    simp [final,GroupedBalancedSignUpperH2Ready67.readyState,execInstrBr,
      MachineState.getReg_setReg_ne]
  refine ⟨final,?_,rpc,?_,?_,?_,source,bits,destination,service,?_,?_⟩
  · have first := Keygen.ordinary_trans image s (layout s) m 41
      (stepsFor ((layout s).getReg .x19)) ltrace choose
    have full := Keygen.ordinary_trans image s m final
      (stepsFor ((layout s).getReg .x19) + 41) 6
      first rtrace
    rw [GroupedBalancedSignUpperH2Layout67.prepared_x19 s] at full
    have countEq : 6 + (stepsFor (s.getReg .x19) + 41) =
        47 + stepsFor (s.getReg .x19) := by omega
    simpa only [countEq] using full
  · rw [x20,max,GroupedBalancedSignUpperH2Layout67.prepared_x19]
  · rw [x21,step]
  · rw [x19,chain,GroupedBalancedSignUpperH2Layout67.prepared_x19]
  · simp [final,GroupedBalancedSignUpperH2Ready67.readyState,
      execInstrBr,MachineState.getReg_setReg_ne]
    rw [stack,GroupedBalancedSignUpperH2Layout67.prepared_stack]
  · intro a
    rw [GroupedBalancedSignUpperH2Ready67.ready_frame,mframe]

theorem prepared_query (s final : MachineState)
    (base leaf chain : Nat) (value : Reference.Digest)
    (level : s.getMem 0x81000 = BitVec.ofNat 64 base)
    (chainWord : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (valueWords : ∀ j : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 j.val) =
        value.extractLsb' (64*j.val) 64)
    (source : final.getReg .x10 = 0x80000)
    (bits : final.getReg .x11 = 384)
    (mem : ∀ a, final.getMem a = (layout s).getMem a) :
    hashInput final =
      Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 base 0 chain 0) leaf value) := by
  apply KeygenDomain.query_eq final _ leaf value source bits
  apply KeygenDomain.words_of_layout final
    (KeygenDomain.header 2 base 0 chain 0) leaf value
  · rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_header s base chain level chainWord
  · intro j
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_index s leaf address j
  · intro j
    rw [mem]
    exact GroupedBalancedSignUpperH2Layout67.prepared_value s value valueWords j

#print axioms prepare
#print axioms prepared_query
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Prepared67
