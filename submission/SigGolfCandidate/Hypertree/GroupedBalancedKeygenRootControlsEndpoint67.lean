import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenChainStep67

/-! The WOTS endpoint copy also preserves the two high tree-address words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsEndpoint67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsChain67
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem copy_control (s : MachineState) (n : Nat)
    (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    ControlFrame s (copyState s) := by
  have addr := address_eq s n counter
  have nextAddr : address s + 8 = BitVec.ofNat 64 (0x80800+16*n+8) := by
    rw [addr]
    change BitVec.ofNat 64 (0x80800+16*n) + BitVec.ofNat 64 8 = _
    rw [←BitVec.ofNat_add]
  have ne (a : Word) (ha : a = 0x81010 ∨ a = 0x81018)
      (m : Nat) (mRange : m ≤ 0x80800+16*66+8) : a ≠ BitVec.ofNat 64 m := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    have mSmall : m < 2^64 := by omega
    rcases ha with rfl | rfl
    · have val : (0x81010 : Word).toNat = 0x81010 := by decide
      rw [val] at hn
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt mSmall] at hn
      omega
    · have val : (0x81018 : Word).toNat = 0x81018 := by decide
      rw [val] at hn
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt mSmall] at hn
      omega
  have one (a : Word) (ha : a = 0x81010 ∨ a = 0x81018) :
      (copyState s).getMem a = s.getMem a := by
    rw [copy_mem s a]
    have neCounter : a ≠ (0x81030 : Word) := by
      rcases ha with rfl | rfl <;> decide
    have neNext : a ≠ address s + (8 : Word) := by
      rw [nextAddr]
      exact ne a ha _ (by omega)
    have neBase : a ≠ address s := by
      rw [addr]
      exact ne a ha _ (by omega)
    simp only [if_neg neCounter,if_neg neNext,if_neg neBase]
  exact ⟨one 0x81010 (Or.inl rfl),one 0x81018 (Or.inr rfl)⟩

theorem copy_after_prefix_control (hash : Hash)
    (s ready final : MachineState) (n pSteps pCycles calls blocks : Nat)
    (bound : n < 67)
    (prefixTrace : Trace hash image s pSteps pCycles calls blocks ready)
    (prefixFrame : ControlFrame s ready)
    (readyPC : ready.pc = 0x12d0)
    (counter : ready.getMem 0x81030 = BitVec.ofNat 64 n)
    (trace : Trace hash image s (pSteps+19) (pCycles+19) calls blocks final) :
    ControlFrame s final := by
  obtain ⟨safe,safeNext⟩ := address_safe ready n bound counter
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s (pSteps+19) (pCycles+19) calls blocks made := by
    simpa only [Nat.add_zero] using prefixTrace.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  exact prefixFrame.trans (copy_control ready n bound counter)

theorem regular_step_control (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x11d8) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : s.getReg .x19 = BitVec.ofNat 64 n)
    (trace : Trace hash image s 86 107 3 3 final) :
    ControlFrame s final := by
  have not65 : s.getReg .x19 ≠ 65#64 := by
    rw [index]
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat] at hn
    omega
  have not66 : s.getReg .x19 ≠ 66#64 := by
    rw [index]
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat] at hn
    omega
  obtain ⟨ready,prefixTrace,readyPC,_,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.regular_from_entry hash s pc not65 not66
  have readyWord : ready.getMem 0x81030 = BitVec.ofNat 64 n :=
    readyCounter.trans counter
  exact copy_after_prefix_control hash s ready final n 67 88 3 3
    (by omega) prefixTrace
    (regular_from_entry_control hash s ready pc not65 not66 prefixTrace)
    readyPC readyWord (by simpa only [Nat.reduceAdd] using trace)

theorem special65_step_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 65#64)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 105 161 8 8 final) :
    ControlFrame s final := by
  obtain ⟨ready,prefixTrace,readyPC,_,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special65_from_entry hash s pc index
  have readyWord : ready.getMem 0x81030 = 65#64 := readyCounter.trans counter
  exact copy_after_prefix_control hash s ready final 65 86 142 8 8
    (by decide) prefixTrace
    (special65_from_entry_control hash s ready pc index prefixTrace)
    readyPC readyWord (by simpa only [Nat.reduceAdd] using trace)

theorem special66_step_control (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 66#64)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 114 184 10 10 final) :
    ControlFrame s final := by
  obtain ⟨ready,prefixTrace,readyPC,_,readyCounter,_,_⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special66_from_entry hash s pc index
  have readyWord : ready.getMem 0x81030 = 66#64 := readyCounter.trans counter
  exact copy_after_prefix_control hash s ready final 66 95 165 10 10
    (by decide) prefixTrace
    (special66_from_entry_control hash s ready pc index prefixTrace)
    readyPC readyWord (by simpa only [Nat.reduceAdd] using trace)

#print axioms regular_step_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsEndpoint67
