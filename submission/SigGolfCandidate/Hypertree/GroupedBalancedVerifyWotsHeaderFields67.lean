import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderBlock67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainReady67

/-! Register and memory facts at the verifier's first WOTS chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderFields67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsHeaderBlock67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem header_pc (s : MachineState) (pc : s.pc = 0x1518) :
    (headerState s).pc = 0x15d8 := by
  simp [headerState,execInstrBr,pc]

theorem header_witness_ptr (s : MachineState) :
    (headerState s).getReg .x22 = s.getMem 0x81048 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_mem_frame (s : MachineState) (a : Word)
    (h30 : a ≠ 0x81030) (h38 : a ≠ 0x81038)
    (h00 : a ≠ 0x90000) (h08 : a ≠ 0x90008)
    (h10 : a ≠ 0x90010) (h18 : a ≠ 0x90018) :
    (headerState s).getMem a = s.getMem a := by
  have n30 : a ≠ (528432#64) := by simpa using h30
  have n38 : a ≠ (528440#64) := by simpa using h38
  have n00 : a ≠ (589824#64) := by simpa using h00
  have n08 : a ≠ (589832#64) := by simpa using h08
  have n10 : a ≠ (589840#64) := by simpa using h10
  have n18 : a ≠ (589848#64) := by simpa using h18
  simp [headerState,execInstrBr,Expansion.mem_setMem,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,n30,n38,n00,n08,n10,n18]

theorem header_low_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x80020) :
    (headerState s).getMem a = s.getMem a := by
  have low_ne (b : Word) (high : 0x80020 ≤ b.toNat) : a ≠ b := by
    intro eq
    rw [eq] at low
    omega
  apply header_mem_frame
  all_goals exact low_ne _ (by decide)

theorem header_witnesses (s : MachineState) (start : Nat)
    (values : Fin 67 → Reference.Digest)
    (safe : GroupedBalancedByteFastChainReady67.SafeWitnesses start)
    (witnesses : GroupedBalancedByteFastChainReady67.WitnessWords s
      start values) :
    GroupedBalancedByteFastChainReady67.WitnessWords
      (headerState s) start values := by
  intro chain half
  rw [header_low_frame s _ (safe chain half).2]
  exact witnesses chain half

#print axioms header_pc
#print axioms header_witness_ptr
#print axioms header_mem_frame
#print axioms header_low_frame
#print axioms header_witnesses
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderFields67
