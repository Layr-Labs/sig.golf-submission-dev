import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Query67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignImageTransfer67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeRegion67. -/
section
/-! Transport traces confined to the signer's unchanged code prefix to the
byte-table decoder image. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignImageTransfer67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

private abbrev oldImage := GroupedBalancedSignImage67.image
private abbrev byteImage := GroupedBalancedSignImage67Byte.image

inductive TraceBelow (hash : Hash) :
    {s : MachineState} → {steps cycles calls blocks : Nat} →
      {t : MachineState} → Trace hash oldImage s steps cycles calls blocks t → Prop where
  | refl (s : MachineState) : TraceBelow hash (Trace.refl s)
  | ordinary (s next t : MachineState) (instruction : Instruction)
      (steps cycles calls blocks : Nat)
      (hf : fetch oldImage s = some instruction)
      (hs : ordinaryStep s instruction = some next)
      (tail : Trace hash oldImage next steps cycles calls blocks t)
      (low : 0x1000 ≤ s.pc.toNat) (high : s.pc.toNat < 0x20f8)
      (rest : TraceBelow hash tail) :
      TraceBelow hash (Trace.ordinary s next t instruction
        steps cycles calls blocks hf hs tail)
  | hash (s t : MachineState) (steps cycles calls blocks : Nat)
      (hf : fetch oldImage s = some (.base .ECALL))
      (hs : s.getReg .x5 = 1) (hv : hashArgumentsValid s = true)
      (tail : Trace hash oldImage
        (writeHash s (hash (hashInput s))) steps cycles calls blocks t)
      (low : 0x1000 ≤ s.pc.toNat) (high : s.pc.toNat < 0x20f8)
      (rest : TraceBelow hash tail) :
      TraceBelow hash (Trace.hash s t steps cycles calls blocks hf hs hv tail)

theorem TraceBelow.trans {hash : Hash} {s t u : MachineState}
    {steps cycles calls blocks moreSteps moreCycles moreCalls moreBlocks : Nat}
    (first : Trace hash oldImage s steps cycles calls blocks t)
    (second : Trace hash oldImage t moreSteps moreCycles moreCalls moreBlocks u)
    (firstBelow : TraceBelow hash first)
    (secondBelow : TraceBelow hash second) :
    TraceBelow hash (first.trans second) := by
  induction firstBelow with
  | refl => simpa using secondBelow
  | ordinary s next t instruction steps cycles calls blocks hf hs tail low high rest ih =>
      simpa only [Trace.trans, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        TraceBelow.ordinary s next u instruction _ _ _ _ hf hs
          (tail.trans second) low high (ih second secondBelow)
  | hash s t steps cycles calls blocks hf hs hv tail low high rest ih =>
      simpa only [Trace.trans, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        TraceBelow.hash s u _ _ _ _ hf hs hv
          (tail.trans second) low high (ih second secondBelow)

inductive OrdinaryBelow :
    {s : MachineState} → {steps : Nat} → {t : MachineState} →
      OrdinarySteps oldImage s steps t → Prop where
  | refl (s : MachineState) : OrdinaryBelow (OrdinarySteps.refl s)
  | step (s next t : MachineState) (instruction : Instruction) (steps : Nat)
      (hf : fetch oldImage s = some instruction)
      (hs : ordinaryStep s instruction = some next)
      (tail : OrdinarySteps oldImage next steps t)
      (low : 0x1000 ≤ s.pc.toNat) (high : s.pc.toNat < 0x20f8)
      (rest : OrdinaryBelow tail) :
      OrdinaryBelow (OrdinarySteps.step s next t instruction steps hf hs tail)

theorem TraceBelow.of_ordinary_region {hash : Hash} {s t : MachineState}
    {steps : Nat} (block : OrdinarySteps oldImage s steps t)
    (below : OrdinaryBelow block) : TraceBelow hash block.trace := by
  induction below with
  | refl s => exact TraceBelow.refl s
  | step s next t instruction steps hf hs tail low high rest ih =>
      exact TraceBelow.ordinary s next t instruction steps steps 0 0
        hf hs tail.trace low high ih

theorem trace_transfer {hash : Hash} {s t : MachineState}
    {steps cycles calls blocks : Nat}
    (trace : Trace hash oldImage s steps cycles calls blocks t)
    (below : TraceBelow hash trace) :
    Trace hash byteImage s steps cycles calls blocks t := by
  induction below with
  | refl s => exact Trace.refl s
  | ordinary s next t instruction steps cycles calls blocks hf hs tail low high rest ih =>
      exact Trace.ordinary s next t instruction steps cycles calls blocks
        ((GroupedBalancedSignImage67Byte.fetch_prefix s low high).trans hf) hs ih
  | hash s t steps cycles calls blocks hf hs hv tail low high rest ih =>
      exact Trace.hash s t steps cycles calls blocks
        ((GroupedBalancedSignImage67Byte.fetch_prefix s low high).trans hf) hs hv ih

#print axioms trace_transfer
end SigGolfCandidate.Hypertree.GroupedBalancedSignImageTransfer67

end

/-! Static control-flow facts for the shared upper Merkle tree subroutine. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeRegion67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignImageTransfer67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedSignImage67.image

def linear : Instruction → Prop
  | .base (.BEQ _ _ _) | .base (.BNE _ _ _)
  | .base (.BLT _ _ _) | .base (.BGE _ _ _)
  | .base (.BLTU _ _ _) | .base (.BGEU _ _ _)
  | .base (.JAL _ _) | .base (.JALR _ _ _) => False
  | _ => True

theorem linear_pc (s next : MachineState) (instruction : Instruction)
    (shape : linear instruction)
    (step : ordinaryStep s instruction = some next) :
    next.pc = s.pc + 4 := by
  cases instruction with
  | word op rd rs1 rs2 =>
      simp only [ordinaryStep, Option.some.injEq] at step
      rw [← step]
      simp [MachineState.setPC]
  | sraiw rd rs shift =>
      simp only [ordinaryStep, Option.some.injEq] at step
      rw [← step]
      simp [MachineState.setPC]
  | base instr =>
      cases instr <;> simp [linear] at shape <;>
        simp [ordinaryStep, execInstrBr] at step <;>
        rcases step with ⟨_,rfl⟩ <;> simp [MachineState.setPC]

def safeAt (pc : Nat) : Instruction → Bool
  | .base (.BEQ _ _ _) | .base (.BLT _ _ _)
  | .base (.BGE _ _ _) | .base (.BLTU _ _ _)
  | .base (.BGEU _ _ _) | .base (.JAL _ _)
  | .base (.JALR _ _ _) => false
  | .base (.BNE _ _ offset) =>
      (pc == 0x1e90 && offset.toNat == 8172) ||
      (pc == 0x2054 && offset.toNat == 7860) ||
      (pc == 0x20e8 && offset.toNat == 7452)
  | _ => true

def safeWord (pc : Nat) (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | some instruction => safeAt pc instruction
  | none => false

def scanAux : Nat → List (BitVec 32) → Bool
  | _, [] => true
  | pc, word :: rest => safeWord pc word && scanAux (pc+4) rest

private theorem static_scan :
    scanAux 0x1da8 (GroupedBalancedSignImage67.code.drop 874 |>.take 211) = true := by
  decide

theorem scan_get (pc : Nat) (words : List (BitVec 32))
    (check : scanAux pc words = true) (j : Nat) (hj : j < words.length) :
    safeWord (pc+4*j) (words.getD j 0) = true := by
  induction words generalizing pc j with
  | nil => simp at hj
  | cons word rest ih =>
      simp only [scanAux, Bool.and_eq_true] at check
      cases j with
      | zero => simpa using check.1
      | succ k =>
          have hk : k < rest.length := by simpa using hj
          have result := ih (pc+4) check.2 k hk
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem static_at (j : Fin 211) :
    safeWord (0x1da8+4*j.val)
      (GroupedBalancedSignImage67.code.getD (874+j.val) 0) = true := by
  have len : (GroupedBalancedSignImage67.code.drop 874 |>.take 211).length = 211 := by
    simp [List.length_take, List.length_drop, GroupedBalancedSignImage67.code_length]
  have result := scan_get 0x1da8
    (GroupedBalancedSignImage67.code.drop 874 |>.take 211)
    static_scan j.val (by rw [len]; exact j.isLt)
  simpa only [List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt j.isLt, List.getElem?_drop, Nat.add_comm] using result

theorem safe_step (s next : MachineState) (instruction : Instruction)
    (pcLow : 0x1da8 ≤ s.pc.toNat) (pcHigh : s.pc.toNat < 0x20f4)
    (safe : safeAt s.pc.toNat instruction = true)
    (step : ordinaryStep s instruction = some next) :
    0x1da8 ≤ next.pc.toNat ∧ next.pc.toNat ≤ s.pc.toNat+4 := by
  by_cases lin : linear instruction
  · have hp := linear_pc s next instruction lin step
    rw [hp, BitVec.toNat_add]
    have hsmall : (s.pc.toNat+4) % 2^64 = s.pc.toNat+4 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [show (4 : Word).toNat = 4 by decide, hsmall]
    omega
  · cases instruction with
    | word op rd rs1 rs2 => simp [linear] at lin
    | sraiw rd rs shift => simp [linear] at lin
    | base instr =>
        cases instr <;> simp [linear, safeAt] at lin safe
        rename_i rs1 rs2 offset
        rcases safe with (⟨hpc,hoff⟩ | ⟨hpc,hoff⟩) | ⟨hpc,hoff⟩
        · have hp : s.pc = (0x1e90 : Word) := BitVec.eq_of_toNat_eq (by simpa using hpc)
          have ho : offset = (8172 : BitVec 13) := BitVec.eq_of_toNat_eq (by simpa using hoff)
          simp [ordinaryStep, memoryArgumentsValid, execInstrBr,
            hp, ho, signExtend13] at step
          split_ifs at step <;> cases step <;> simp [hp, MachineState.setPC]

        · have hp : s.pc = (0x2054 : Word) := BitVec.eq_of_toNat_eq (by simpa using hpc)
          have ho : offset = (7860 : BitVec 13) := BitVec.eq_of_toNat_eq (by simpa using hoff)
          simp [ordinaryStep, memoryArgumentsValid, execInstrBr,
            hp, ho, signExtend13] at step
          split_ifs at step <;> cases step <;> simp [hp, MachineState.setPC]
        · have hp : s.pc = (0x20e8 : Word) := BitVec.eq_of_toNat_eq (by simpa using hpc)
          have ho : offset = (7452 : BitVec 13) := BitVec.eq_of_toNat_eq (by simpa using hoff)
          simp [ordinaryStep, memoryArgumentsValid, execInstrBr,
            hp, ho, signExtend13] at step
          split_ifs at step <;> cases step <;> simp [hp, MachineState.setPC]

theorem region_fetch_safe (s : MachineState) (instruction : Instruction)
    (low : 0x1da8 ≤ s.pc.toNat) (high : s.pc.toNat < 0x20f4)
    (hf : fetch image s = some instruction) :
    safeAt s.pc.toNat instruction = true := by
  have aligned : s.pc.toNat % 4 = 0 := by
    by_contra h
    have empty : fetch image s = none := by simp [fetch, h]
    rw [empty] at hf
    contradiction
  let j : Fin 211 := ⟨(s.pc.toNat-0x1da8)/4, by omega⟩
  have hpc : 0x1da8+4*j.val = s.pc.toNat := by dsimp [j]; omega
  have hidx : 874+j.val = (s.pc.toNat-0x1000)/4 := by dsimp [j]; omega
  have hs := static_at j
  rw [hpc, hidx] at hs
  have idxBound : (s.pc.toNat-0x1000)/4 < GroupedBalancedSignImage67.code.length := by
    rw [GroupedBalancedSignImage67.code_length]
    omega
  have hf' : decodeInstruction
      (GroupedBalancedSignImage67.code.getD ((s.pc.toNat-0x1000)/4) 0) =
      some instruction := by
    have htest : ¬(s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) := by
      simp [show ¬ s.pc.toNat < 0x1000 by omega, aligned]
    have decoded : decodeInstruction
        GroupedBalancedSignImage67.code[(s.pc.toNat-0x1000)/4] =
        some instruction := by
      simpa [fetch, GroupedBalancedSignImage67.image, htest,
        List.getElem?_eq_getElem idxBound] using hf
    simpa [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem idxBound] using decoded
  change (match decodeInstruction
      (GroupedBalancedSignImage67.code.getD ((s.pc.toNat-0x1000)/4) 0) with
    | some found => safeAt s.pc.toNat found
    | none => false) = true at hs
  rw [hf'] at hs
  exact hs

theorem trace_below_region {hash : Hash} {s t : MachineState}
    {steps cycles calls blocks : Nat}
    (trace : Trace hash image s steps cycles calls blocks t)
    (low : 0x1da8 ≤ s.pc.toNat)
    (bounded : s.pc.toNat + 4*steps < 0x20f4) :
    TraceBelow hash trace := by
  induction trace with
  | refl state => exact TraceBelow.refl state
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      have sourceHigh : state.pc.toNat < 0x20f4 := by omega
      have safe := region_fetch_safe state instruction low sourceHigh hf
      obtain ⟨nextLow,nextBound⟩ := safe_step state next instruction
        low sourceHigh safe hs
      have nextHigh : next.pc.toNat + 4*steps < 0x20f4 := by omega
      exact TraceBelow.ordinary state next final instruction steps cycles calls blocks
        hf hs tail (by omega) (by omega) (ih nextLow nextHigh)
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      have nextPc :
          (writeHash state (hash (hashInput state))).pc.toNat =
            state.pc.toNat+4 := by
        rw [Keygen.hash_pc, BitVec.toNat_add]
        simp only [show (4 : Word).toNat = 4 by decide]
        exact Nat.mod_eq_of_lt (by omega)
      have nextLow : 0x1da8 ≤
          (writeHash state (hash (hashInput state))).pc.toNat := by
        rw [nextPc]
        omega
      have nextHigh :
          (writeHash state (hash (hashInput state))).pc.toNat + 4*steps < 0x20f4 := by
        rw [nextPc]
        omega
      exact TraceBelow.hash state final steps cycles calls blocks hf hs hv tail
        (by omega) (by omega) (ih nextLow nextHigh)

theorem trace_below_zero {hash : Hash} {s t : MachineState}
    {cycles calls blocks : Nat}
    (trace : Trace hash image s 0 cycles calls blocks t) :
    TraceBelow hash trace := by
  cases trace with
  | refl => exact TraceBelow.refl s

theorem trace_below_len {hash : Hash} {s t : MachineState}
    {steps cycles calls blocks : Nat}
    (trace : Trace hash image s steps cycles calls blocks t)
    (low : 0x1da8 ≤ s.pc.toNat)
    (bounded : s.pc.toNat + 4*steps ≤ 0x20f8) :
    TraceBelow hash trace := by
  induction trace with
  | refl state => exact TraceBelow.refl state
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      have sourceHigh : state.pc.toNat < 0x20f8 := by omega
      cases steps with
      | zero =>
          exact TraceBelow.ordinary state next final instruction 0 cycles calls blocks
            hf hs tail (by omega) sourceHigh (trace_below_zero tail)
      | succ k =>
          have sourceBody : state.pc.toNat < 0x20f4 := by omega
          have safe := region_fetch_safe state instruction low sourceBody hf
          obtain ⟨nextLow,nextBound⟩ := safe_step state next instruction
            low sourceBody safe hs
          have nextHigh : next.pc.toNat + 4*(k+1) ≤ 0x20f8 := by omega
          exact TraceBelow.ordinary state next final instruction (k+1) cycles calls blocks
            hf hs tail (by omega) sourceHigh (ih nextLow nextHigh)
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      have sourceHigh : state.pc.toNat < 0x20f8 := by omega
      cases steps with
      | zero =>
          exact TraceBelow.hash state final 0 cycles calls blocks hf hs hv tail
            (by omega) sourceHigh (trace_below_zero tail)
      | succ k =>
          have nextPc :
              (writeHash state (hash (hashInput state))).pc.toNat =
                state.pc.toNat+4 := by
            rw [Keygen.hash_pc, BitVec.toNat_add]
            simp only [show (4 : Word).toNat = 4 by decide]
            exact Nat.mod_eq_of_lt (by omega)
          have nextLow : 0x1da8 ≤
              (writeHash state (hash (hashInput state))).pc.toNat := by
            rw [nextPc]
            omega
          have nextHigh :
              (writeHash state (hash (hashInput state))).pc.toNat + 4*(k+1) ≤ 0x20f8 := by
            rw [nextPc]
            omega
          exact TraceBelow.hash state final (k+1) cycles calls blocks hf hs hv tail
            (by omega) sourceHigh (ih nextLow nextHigh)

#print axioms trace_below_region
#print axioms trace_below_len

end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeRegion67
