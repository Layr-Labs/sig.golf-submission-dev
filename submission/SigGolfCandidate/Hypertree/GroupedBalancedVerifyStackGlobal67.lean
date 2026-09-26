import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte
import SigGolfCandidate.Hypertree.KeygenTrace

/-! The direct verifier never writes the stack pointer after its loaded entry. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def LowFrame (s t : MachineState) : Prop :=
  ∀ a : Word, a.toNat < 0x80000 → t.getMem a = s.getMem a

theorem LowFrame.refl (s : MachineState) : LowFrame s s := by
  intro _ _
  rfl

theorem LowFrame.trans {s t u : MachineState}
    (first : LowFrame s t) (second : LowFrame t u) :
    LowFrame s u := by
  intro a low
  exact (second a low).trans (first a low)

theorem low_ne (a : Word) (low : a.toNat < 0x80000)
    (b : Nat) (ge : 0x80000 ≤ b) (bound : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have value := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound] at value
  omega

def baseDest? : Instr → Option Reg
  | .ADD rd _ _ | .SUB rd _ _ | .SLL rd _ _ | .SRL rd _ _
  | .SRA rd _ _ | .AND rd _ _ | .OR rd _ _ | .XOR rd _ _
  | .SLT rd _ _ | .SLTU rd _ _ | .SUBW rd _ _ | .SRLW rd _ _
  | .MUL rd _ _ | .MULH rd _ _ | .MULHSU rd _ _ | .MULHU rd _ _
  | .DIV rd _ _ | .DIVU rd _ _ | .REM rd _ _ | .REMU rd _ _ => some rd
  | .ADDI rd _ _ | .ANDI rd _ _ | .ORI rd _ _ | .XORI rd _ _
  | .SLTI rd _ _ | .SLTIU rd _ _ | .SLLI rd _ _ | .SRLI rd _ _
  | .SRAI rd _ _ | .LD rd _ _ | .LW rd _ _ | .LWU rd _ _
  | .LB rd _ _ | .LH rd _ _ | .LBU rd _ _ | .LHU rd _ _
  | .JALR rd _ _ | .MV rd _ | .ADDIW rd _ _ | .SLLIW rd _ _
  | .SRLIW rd _ _ => some rd
  | .LUI rd _ | .AUIPC rd _ | .JAL rd _ | .LI rd _ => some rd
  | .SD _ _ _ | .SW _ _ _ | .SB _ _ _ | .SH _ _ _
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _
  | .BLTU _ _ _ | .BGEU _ _ _ | .NOP | .ECALL | .FENCE
  | .EBREAK => none
  | .CSRS _ _ => some .x2

def dest? : Instruction → Option Reg
  | .base inst => baseDest? inst
  | .word _ rd _ _ => some rd
  | .sraiw rd _ _ => some rd

def StackSafe (inst : Instruction) : Prop := dest? inst ≠ some .x2

instance (inst : Instruction) : Decidable (StackSafe inst) :=
  inferInstanceAs (Decidable (dest? inst ≠ some .x2))

theorem base_exec_stack (s : MachineState) (inst : Instr)
    (safe : baseDest? inst ≠ some .x2) :
    (execInstrBr s inst).getReg .x2 = s.getReg .x2 := by
  cases inst <;>
    simp_all [baseDest?,execInstrBr,MachineState.getReg_setReg_ne,
      MachineState.setMem,MachineState.setByte,MachineState.setHalfword,
      MachineState.setWord32]
  all_goals simp [MachineState.getReg,MachineState.setPC]
  all_goals split_ifs <;> simp_all

theorem ordinary_stack (s next : MachineState) (inst : Instruction)
    (safe : StackSafe inst)
    (step : ordinaryStep s inst = some next) :
    next.getReg .x2 = s.getReg .x2 := by
  cases inst with
  | base base =>
      cases base <;> simp_all [ordinaryStep]
      all_goals
        rw [← step.2]
        apply base_exec_stack
        simpa [StackSafe,dest?] using safe
  | word op rd rs1 rs2 =>
      have ne : rd ≠ .x2 := by
        simpa [StackSafe,dest?] using safe
      simp only [ordinaryStep,Option.some.injEq] at step
      subst next
      simp [MachineState.getReg_setReg_ne _ rd .x2 _ ne]
  | sraiw rd rs shift =>
      have ne : rd ≠ .x2 := by
        simpa [StackSafe,dest?] using safe
      simp only [ordinaryStep,Option.some.injEq] at step
      subst next
      simp [MachineState.getReg_setReg_ne _ rd .x2 _ ne]

def codeSafe : Bool :=
  image.code.all fun raw =>
    ((decodeInstruction raw).map fun inst => decide (StackSafe inst)).getD true

theorem code_safe : codeSafe = true := by decide

theorem safe_fetch (s : MachineState) (inst : Instruction)
    (fetched : fetch image s = some inst) : StackSafe inst := by
  unfold fetch at fetched
  split at fetched
  · simp at fetched
  · cases hcode : image.code[(s.pc.toNat - 0x1000) / 4]? with
    | none => simp [hcode] at fetched
    | some raw =>
        have hdecode : decodeInstruction raw = some inst := by
          simpa [hcode] using fetched
        have member : raw ∈ image.code := List.mem_of_getElem? hcode
        have all : image.code.all (fun raw =>
            ((decodeInstruction raw).map fun inst => decide (StackSafe inst)).getD true) =
            true := code_safe
        have check := (List.all_eq_true.mp all) raw member
        simp only [hdecode,Option.map_some,Option.getD_some] at check
        exact of_decide_eq_true check

theorem hash_stack (s : MachineState) (answer : BitVec 256) :
    (writeHash s answer).getReg .x2 = s.getReg .x2 := by
  simp only [writeHash,MachineState.getReg_setPC,
    MachineState.getReg_writeWords]

theorem trace_stack (hash : Hash) {s t : MachineState}
    {steps cycles calls blocks : Nat}
    (run : Trace hash image s steps cycles calls blocks t) :
    t.getReg .x2 = s.getReg .x2 := by
  induction run with
  | refl => rfl
  | ordinary state next final inst _ _ _ _ fetched step tail ih =>
      exact ih.trans (ordinary_stack state next inst
        (safe_fetch state inst fetched) step)
  | hash state final _ _ _ _ fetched service valid tail ih =>
      exact ih.trans (hash_stack state (hash (hashInput state)))

#print axioms trace_stack

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyStackGlobal67
