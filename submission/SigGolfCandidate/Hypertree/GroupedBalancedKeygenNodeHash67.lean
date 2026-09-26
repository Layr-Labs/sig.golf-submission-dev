import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHeader67

/-! Control words preserved through one H4 keygen node. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeControls67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem prelude_control (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81008#64) (h1 : a ≠ 0x80020#64)
    (h2 : a ≠ 0x80028#64) (h3 : a ≠ 0x80030#64)
    (h4 : a ≠ 0x80038#64) :
    (GroupedBalancedKeygenNodePrelude67.preludeState s).getMem a = s.getMem a := by
  simp [GroupedBalancedKeygenNodePrelude67.preludeState,execInstrBr,signExtend12,
    h0,h1,h2,h3,h4,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_control (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000#64) (h1 : a ≠ 0x80008#64)
    (h2 : a ≠ 0x80010#64) (h3 : a ≠ 0x80018#64) :
    (GroupedBalancedKeygenNodeHeader67.headerState s).getMem a = s.getMem a := by
  simp [GroupedBalancedKeygenNodeHeader67.headerState,execInstrBr,signExtend12,
    h0,h1,h2,h3,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem hash_control (hash : Hash) (s : MachineState) (a : Word)
    (dst : s.getReg .x12 = 0x80300)
    (high : 0x81000 ≤ a.toNat) :
    (writeHash s (hash (hashInput s))).getMem a = s.getMem a := by
  apply Signing.hash_answer_frame s (hash (hashInput s)) dst a
  intro i same
  have hn := congrArg BitVec.toNat same
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
  omega
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeControls67


/-! Actual H4 hash call for a direct67 keygen internal tree node. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem hash_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1558)
    (fields : s.getReg .x5 = 1 ∧ s.getReg .x10 = 0x80000 ∧
      s.getReg .x11 = 512 ∧ s.getReg .x12 = 0x80300) :
    Trace hash image s 1 8 1 1 (writeHash s (hash (hashInput s))) := by
  have code : fetch image s = some (.base .ECALL) := by
    have hc : Keygen.instructionAt image 0x1558 = some (.base .ECALL) := by
      unfold image GroupedBalancedKeygenImage67.image
      decide
    change Keygen.instructionAt image s.pc = some (.base .ECALL)
    rw [pc]
    exact hc
  obtain ⟨service,source,bits,destination⟩ := fields
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,source,bits,destination,
      accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput s).1 = 512 := by simp [hashInput,bits]
  simpa [len,compressions] using
    Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

theorem prelude_header_hash (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1480)
    (safe0 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64) 8 = true)
    (safe1 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 8#64) 8 = true)
    (safe2 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 16#64) 8 = true)
    (safe3 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 24#64) 8 = true) :
    ∃ final,
      Trace hash image s 55 62 1 1 final ∧
      final.pc = 0x155c ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a ≠ 0x81008#64 →
        final.getMem a = s.getMem a) := by
  let prepared := GroupedBalancedKeygenNodePrelude67.preludeState s
  have first : Trace hash image s 21 21 0 0 prepared :=
    (GroupedBalancedKeygenNodePrelude67.prelude_steps s pc
      safe0 safe1 safe2 safe3).trace
  have preparedPC := GroupedBalancedKeygenNodePrelude67.prelude_pc s pc
  let ready := GroupedBalancedKeygenNodeHeader67.headerState prepared
  have second : Trace hash image prepared 33 33 0 0 ready :=
    (GroupedBalancedKeygenNodeHeader67.header_steps prepared preparedPC).trace
  have readyPC := GroupedBalancedKeygenNodeHeader67.header_pc prepared preparedPC
  have readyRegs := GroupedBalancedKeygenNodeHeader67.header_regs prepared
  let final := writeHash ready (hash (hashInput ready))
  have third : Trace hash image ready 1 8 1 1 final :=
    hash_trace hash ready readyPC readyRegs
  refine ⟨final,by simpa only [Nat.reduceAdd] using (first.trans second).trans third,
    by change ready.pc+4 = 0x155c; rw [readyPC]; decide,?_⟩
  intro a high ne08
  have ne (b : Nat) (below : b < 0x81000) : a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  have preparedHigh : prepared.getMem a = s.getMem a :=
    GroupedBalancedKeygenNodeControls67.prelude_control s a
      ne08 (ne 0x80020 (by decide))
      (ne 0x80028 (by decide)) (ne 0x80030 (by decide))
      (ne 0x80038 (by decide))
  have readyHigh : ready.getMem a = prepared.getMem a :=
    GroupedBalancedKeygenNodeControls67.header_control prepared a
      (ne 0x80000 (by decide)) (ne 0x80008 (by decide))
      (ne 0x80010 (by decide)) (ne 0x80018 (by decide))
  have finalHigh : final.getMem a = ready.getMem a :=
    GroupedBalancedKeygenNodeControls67.hash_control hash ready a
      readyRegs.2.2.2 (by omega)
  exact finalHigh.trans (readyHigh.trans preparedHigh)

#print axioms hash_trace
#print axioms prelude_header_hash

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHash67
