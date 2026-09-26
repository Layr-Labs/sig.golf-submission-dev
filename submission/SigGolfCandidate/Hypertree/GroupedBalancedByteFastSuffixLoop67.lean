import SigGolfCandidate.Hypertree.GroupedBalancedChecksum67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte
import SigGolfCandidate.Hypertree.KeygenTrace
import SigGolfCandidate.Hypertree.VerifyHoistLoop


/-! Cycle target for the register-resident 67-chain verifier. The formula
matches the independent RV64 emulator, including the 11-cycle cost of each
suffix hash, one extra decoder instruction on a non-flipped digest, and one
extra instruction per right Merkle edge. A universal bytecode refinement to
this formula remains a separate obligation. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedFastCycleModel67
open SigGolf SigGolfCandidate.Hypertree Reference

def groupCycles (digest : Digest) : Nat :=
  11 * GroupedBalancedChecksum67.suffixCost digest +
    if GroupedBalancedQuaternary.needsFlip digest then 0 else 1

theorem group_cycles_le (digest : Digest) : groupCycles digest ≤ 1079 := by
  have suffix := GroupedBalancedChecksum67.suffix_cost_le digest
  by_cases flip : GroupedBalancedQuaternary.needsFlip digest
  · simp only [groupCycles, if_pos flip]
    omega
  · simp only [groupCycles, if_neg flip]
    omega

theorem groups_cycles_le (digests : List Digest) :
    (digests.map groupCycles).sum ≤ 1079 * digests.length := by
  induction digests with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have bound := group_cycles_le head
      omega

def verifierCycles (digests : List Digest) (rightEdges : Nat) : Nat :=
  103431 + (digests.map groupCycles).sum + rightEdges

theorem verifier_cycle_target (digests : List Digest) (rightEdges : Nat)
    (groups : digests.length = 45) (path : rightEdges ≤ 160) :
    verifierCycles digests rightEdges ≤ 152146 := by
  have bound := groups_cycles_le digests
  simp only [verifierCycles]
  omega

end SigGolfCandidate.Hypertree.GroupedBalancedFastCycleModel67


/-!
The actual Fast2 verifier's WOTS suffix loop occupies PCs 0x162c–0x163c.
This module proves its raw RV64 instruction shape and a universal cycle trace
for a chain endpoint of 3, 8, or 10. Functional hash-input refinement is
separate from this local resource certificate.
-/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Verifying
open Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def SuffixCode (image : Image) : Prop :=
  instructionAt image 0x162c = some (.base (.BEQ .x21 .x20 20)) ∧
  instructionAt image 0x1630 = some (.base (.SB .x10 .x21 4)) ∧
  instructionAt image 0x1634 = some (.base .ECALL) ∧
  instructionAt image 0x1638 = some (.base (.ADDI .x21 .x21 1)) ∧
  instructionAt image 0x163c = some (.base (.BNE .x21 .x20 (-12)))

theorem concrete_code : SuffixCode image := by
  unfold SuffixCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

structure Fields (s : MachineState) (step limit : Nat) : Prop where
  service : s.getReg .x5 = 1
  src : s.getReg .x10 = 0x90000
  len : s.getReg .x11 = 384
  dst : s.getReg .x12 = 0x90020
  stepReg : s.getReg .x21 = BitVec.ofNat 64 step
  limitReg : s.getReg .x20 = BitVec.ofNat 64 limit

def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BEQ .x21 .x20 20)

def tickState (hash : Hash) (s : MachineState) : MachineState :=
  let stored := execInstrBr s (.SB .x10 .x21 4)
  let hashed := writeHash stored (hash (hashInput stored))
  let next := execInstrBr hashed (.ADDI .x21 .x21 1)
  execInstrBr next (.BNE .x21 .x20 (-12))

theorem branch_block (code : SuffixCode image) (s : MachineState)
    (pc : s.pc = 0x162c) :
    OrdinarySteps image s 1 (branchState s) := by
  apply OrdinarySteps.step s _ _ (.base (.BEQ .x21 .x20 20)) 0
  · simpa only [fetch_at, pc] using code.1
  · rfl
  exact OrdinarySteps.refl _

theorem branch_pc (s : MachineState) (step limit : Nat)
    (pc : s.pc = 0x162c) (fields : Fields s step limit)
    (stepBound : step ≤ limit) (limitBound : limit ≤ 10) :
    (branchState s).pc = if step = limit then 0x1640 else 0x1630 := by
  simp [branchState, execInstrBr, MachineState.setPC, signExtend13, pc,
    fields.stepReg, fields.limitReg]
  interval_cases limit <;> interval_cases step <;> decide

theorem tick_block (hash : Hash) (code : SuffixCode image)
    (s : MachineState) (step limit : Nat)
    (pc : s.pc = 0x1630) (fields : Fields s step limit) :
    Trace hash image s 4 11 1 1 (tickState hash s) := by
  let stored := execInstrBr s (.SB .x10 .x21 4)
  let hashed := writeHash stored (hash (hashInput stored))
  let advanced := execInstrBr hashed (.ADDI .x21 .x21 1)
  have storedPC : stored.pc = 0x1634 := by
    simp [stored, execInstrBr, MachineState.setPC, pc]
  have storedRegs : stored.getReg .x5 = 1 ∧
      stored.getReg .x10 = 0x90000 ∧ stored.getReg .x11 = 384 ∧
      stored.getReg .x12 = 0x90020 := by
    simp [stored, execInstrBr, MachineState.setByte,
      fields.service, fields.src, fields.len, fields.dst]
  have store : OrdinarySteps image s 1 stored := by
    apply OrdinarySteps.step s stored _ (.base (.SB .x10 .x21 4)) 0
    · simpa only [fetch_at, pc] using code.2.1
    · simp [stored, ordinaryStep, memoryArgumentsValid,
        execInstrBr, fields.src, signExtend12, accessValid,
        rangeValid, MEMORY_BYTES]
    exact OrdinarySteps.refl _
  have hfetch : fetch image stored = some (.base .ECALL) := by
    simpa only [fetch_at, storedPC] using code.2.2.1
  have valid : hashArgumentsValid stored = true := by
    simp [hashArgumentsValid, storedRegs.2.1, storedRegs.2.2.1,
      storedRegs.2.2.2, accessValid, rangeValid, MEMORY_BYTES]
  have hlen : (hashInput stored).1 = 384 := by
    simp [hashInput, storedRegs.2.2.1]
  have hashedPC : hashed.pc = 0x1638 := by
    simp [hashed, Keygen.hash_pc, storedPC]
  have hashedTrace : Trace hash image stored 1 8 1 1 hashed := by
    simpa [hashed, hlen, compressions] using
      Trace.hash stored hashed 0 0 0 0 hfetch storedRegs.1 valid
        (Trace.refl hashed)
  have advancedPC : advanced.pc = 0x163c := by
    simp [advanced, execInstrBr, MachineState.setPC, hashedPC]
  have post : OrdinarySteps image hashed 2 (tickState hash s) := by
    apply OrdinarySteps.step hashed advanced _ (.base (.ADDI .x21 .x21 1)) 1
    · simpa only [fetch_at, hashedPC] using code.2.2.2.1
    · rfl
    apply OrdinarySteps.step advanced (tickState hash s) _
      (.base (.BNE .x21 .x20 (-12))) 0
    · simpa only [fetch_at, advancedPC] using code.2.2.2.2
    · rfl
    exact OrdinarySteps.refl _
  simpa [Nat.add_assoc] using store.trace.trans (hashedTrace.trans post.trace)

theorem tick_regs (hash : Hash) (s : MachineState) (r : Reg)
    (other : r ≠ .x21) :
    (tickState hash s).getReg r = s.getReg r := by
  simp [tickState, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm other),
    Keygen.hash_registers]

theorem tick_step_reg (hash : Hash) (s : MachineState) :
    (tickState hash s).getReg .x21 = s.getReg .x21 + 1 := by
  simp [tickState, execInstrBr, MachineState.setByte,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    Keygen.hash_registers, signExtend12]

theorem tick_fields (hash : Hash) (s : MachineState) (step limit : Nat)
    (fields : Fields s step limit) :
    Fields (tickState hash s) (step + 1) limit := by
  refine ⟨(tick_regs hash s .x5 (by decide)).trans fields.service,
    (tick_regs hash s .x10 (by decide)).trans fields.src,
    (tick_regs hash s .x11 (by decide)).trans fields.len,
    (tick_regs hash s .x12 (by decide)).trans fields.dst,
    ?_, (tick_regs hash s .x20 (by decide)).trans fields.limitReg⟩
  rw [tick_step_reg, fields.stepReg]
  exact (BitVec.ofNat_add step 1).symm

private theorem bne_regs (u : MachineState) (r : Reg) :
    (execInstrBr u (.BNE .x21 .x20 (-12))).getReg r = u.getReg r := by
  simp [execInstrBr]

private theorem bne_pc (u : MachineState) (step limit : Nat)
    (pc : u.pc = 0x163c)
    (stepReg : u.getReg .x21 = BitVec.ofNat 64 (step + 1))
    (limitReg : u.getReg .x20 = BitVec.ofNat 64 limit)
    (small : step < limit) (limitBound : limit ≤ 10) :
    (execInstrBr u (.BNE .x21 .x20 (-12))).pc =
      if step + 1 = limit then 0x1640 else 0x1630 := by
  simp [execInstrBr, MachineState.setPC, signExtend13,
    pc, stepReg, limitReg]
  interval_cases limit <;> interval_cases step <;> decide

theorem tick_pc (hash : Hash) (s : MachineState) (step limit : Nat)
    (pc : s.pc = 0x1630) (fields : Fields s step limit)
    (small : step < limit) (limitBound : limit ≤ 10) :
    (tickState hash s).pc =
      if step + 1 = limit then 0x1640 else 0x1630 := by
  let stored := execInstrBr s (.SB .x10 .x21 4)
  let hashed := writeHash stored (hash (hashInput stored))
  let advanced := execInstrBr hashed (.ADDI .x21 .x21 1)
  have storedPC : stored.pc = 0x1634 := by
    simp [stored, execInstrBr, MachineState.setPC, pc]
  have hashedPC : hashed.pc = 0x1638 := by
    rw [Keygen.hash_pc, storedPC]
    decide
  have advancedPC : advanced.pc = 0x163c := by
    simp [advanced, execInstrBr, MachineState.setPC, hashedPC]
  have advancedStep : advanced.getReg .x21 = BitVec.ofNat 64 (step + 1) := by
    have h := tick_step_reg hash s
    change (execInstrBr advanced (.BNE .x21 .x20 (-12))).getReg .x21 =
      s.getReg .x21 + 1 at h
    rw [bne_regs, fields.stepReg] at h
    exact h.trans (BitVec.ofNat_add step 1).symm
  have advancedLimit : advanced.getReg .x20 = BitVec.ofNat 64 limit := by
    have h := tick_regs hash s .x20 (by decide)
    change (execInstrBr advanced (.BNE .x21 .x20 (-12))).getReg .x20 =
      s.getReg .x20 at h
    rw [bne_regs] at h
    exact h.trans fields.limitReg
  change (execInstrBr advanced (.BNE .x21 .x20 (-12))).pc = _
  exact bne_pc advanced step limit advancedPC advancedStep advancedLimit
    small limitBound

theorem branch_regs (s : MachineState) (r : Reg) :
    (branchState s).getReg r = s.getReg r := by
  simp [branchState, execInstrBr]

theorem branch_fields (s : MachineState) (step limit : Nat)
    (fields : Fields s step limit) :
    Fields (branchState s) step limit := by
  refine ⟨(branch_regs s .x5).trans fields.service,
    (branch_regs s .x10).trans fields.src,
    (branch_regs s .x11).trans fields.len,
    (branch_regs s .x12).trans fields.dst,
    (branch_regs s .x21).trans fields.stepReg,
    (branch_regs s .x20).trans fields.limitReg⟩

theorem hash_loop (hash : Hash) (s : MachineState)
    (step limit remaining : Nat)
    (pc : s.pc = 0x1630)
    (length : step + remaining = limit)
    (positive : 0 < remaining) (limitBound : limit ≤ 10)
    (fields : Fields s step limit) :
    ∃ final,
      Trace hash image s (4 * remaining) (11 * remaining)
        remaining remaining final ∧
      final.pc = 0x1640 ∧ Fields final limit limit := by
  induction remaining generalizing s step with
  | zero => omega
  | succ remaining ih =>
      have small : step < limit := by omega
      let next := tickState hash s
      have tick := tick_block hash concrete_code s step limit pc fields
      have nextFields := tick_fields hash s step limit fields
      by_cases zero : remaining = 0
      · subst remaining
        have last : step + 1 = limit := by omega
        have nextPC : next.pc = 0x1640 := by
          rw [tick_pc hash s step limit pc fields small limitBound]
          simp [last]
        refine ⟨next, ?_, nextPC, ?_⟩
        · simpa using tick
        · simpa only [last] using nextFields
      · have notLast : step + 1 ≠ limit := by omega
        have nextPC : next.pc = 0x1630 := by
          rw [tick_pc hash s step limit pc fields small limitBound]
          simp [notLast]
        obtain ⟨final, tail, finalPC, finalFields⟩ :=
          ih next (step + 1) nextPC (by omega) (by omega)
            nextFields
        refine ⟨final, ?_, finalPC, finalFields⟩
        convert tick.trans tail using 1 <;> omega

/-- Exact local cycle cost of Fast2's selected WOTS suffix, for every hash
answer history and every legal endpoint value. -/
theorem run_suffix (hash : Hash) (s : MachineState)
    (step limit : Nat)
    (pc : s.pc = 0x162c)
    (stepBound : step ≤ limit) (limitBound : limit ≤ 10)
    (fields : Fields s step limit) :
    ∃ final,
      Trace hash image s (4 * (limit - step) + 1)
        (11 * (limit - step) + 1)
        (limit - step) (limit - step) final ∧
      final.pc = 0x1640 ∧ Fields final limit limit := by
  have pre := branch_block concrete_code s pc
  let ready := branchState s
  have readyFields := branch_fields s step limit fields
  by_cases zero : limit - step = 0
  · have last : step = limit := by omega
    have readyPC : ready.pc = 0x1640 := by
      rw [branch_pc s step limit pc fields stepBound limitBound]
      simp [last]
    refine ⟨ready, ?_, readyPC, ?_⟩
    · simpa [zero] using pre.trace
    · simpa only [last] using readyFields
  · have notLast : step ≠ limit := by omega
    have readyPC : ready.pc = 0x1630 := by
      rw [branch_pc s step limit pc fields stepBound limitBound]
      simp [notLast]
    obtain ⟨final, tail, finalPC, finalFields⟩ :=
      hash_loop hash ready step limit (limit - step) readyPC
        (by omega) (by omega) limitBound readyFields
    refine ⟨final, ?_, finalPC, finalFields⟩
    convert pre.trace.trans tail using 1 <;> omega

theorem max_digit_le_ten (chain : GroupedBalancedChecksum67.Chain) :
    GroupedBalancedChecksum67.maxDigit chain ≤ 10 := by
  unfold GroupedBalancedChecksum67.maxDigit
  split_ifs <;> omega

theorem run_chain_suffix (hash : Hash) (s : MachineState)
    (message : Reference.Digest) (chain : GroupedBalancedChecksum67.Chain)
    (pc : s.pc = 0x162c)
    (fields : Fields s (GroupedBalancedChecksum67.digit message chain).val
      (GroupedBalancedChecksum67.maxDigit chain)) :
    ∃ final,
      Trace hash image s
        (4 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 1)
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 1)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val)
        (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) final ∧
      final.pc = 0x1640 ∧
      Fields final (GroupedBalancedChecksum67.maxDigit chain)
        (GroupedBalancedChecksum67.maxDigit chain) :=
  run_suffix hash s (GroupedBalancedChecksum67.digit message chain).val
    (GroupedBalancedChecksum67.maxDigit chain) pc
    (GroupedBalancedChecksum67.digit_le_max message chain)
    (max_digit_le_ten chain) fields

/-- The complete 67-chain loop cost is the functional suffix count times
eleven, plus one entry branch per chain. -/
theorem all_chain_suffix_cycles (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      (11 * (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) + 1)) =
      11 * GroupedBalancedChecksum67.suffixCost message + 67 := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [GroupedBalancedChecksum67.suffixCost]

theorem all_chain_suffix_cycles_le (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      (11 * (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) + 1)) ≤
      1145 := by
  rw [all_chain_suffix_cycles]
  have h := GroupedBalancedChecksum67.suffix_cost_le message
  omega

/-- The local RV64 loop cost and the Fast2 group model agree exactly after
accounting for the 67 entry branches in the model's fixed term and the one
conditional decoder instruction in its variable term. -/
theorem group_model_bridge (message : Reference.Digest) :
    (∑ chain : GroupedBalancedChecksum67.Chain,
      (11 * (GroupedBalancedChecksum67.maxDigit chain -
        (GroupedBalancedChecksum67.digit message chain).val) + 1)) +
      (if GroupedBalancedQuaternary.needsFlip message then 0 else 1) =
      GroupedBalancedFastCycleModel67.groupCycles message + 67 := by
  rw [all_chain_suffix_cycles]
  unfold GroupedBalancedFastCycleModel67.groupCycles
  omega

theorem groups_model_bridge (messages : List Reference.Digest) :
    (messages.map fun message =>
      ∑ chain : GroupedBalancedChecksum67.Chain,
        (11 * (GroupedBalancedChecksum67.maxDigit chain -
          (GroupedBalancedChecksum67.digit message chain).val) + 1)).sum +
    (messages.map fun message =>
      if GroupedBalancedQuaternary.needsFlip message then 0 else 1).sum =
    (messages.map GroupedBalancedFastCycleModel67.groupCycles).sum +
      67 * messages.length := by
  induction messages with
  | nil => simp
  | cons message rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have bridge := group_model_bridge message
      omega

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastSuffixLoop67
