import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperPostGroup67

/-! The signer exits after the final upper tree has been constructed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperFinish67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def successState (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.ADDI .x5 .x0 0)) (.ADDI .x10 .x0 1)

private theorem success_code :
    Keygen.instructionAt image 0x1d60 = some (.base (.ADDI .x5 .x0 0)) ∧
    Keygen.instructionAt image 0x1d64 = some (.base (.ADDI .x10 .x0 1)) ∧
    Keygen.instructionAt image 0x1d68 = some (.base .ECALL) := by decide

theorem success_steps (s : MachineState) (pc : s.pc=0x1d60) :
    OrdinarySteps image s 2 (successState s) := by
  obtain ⟨c0,c1,_⟩ := success_code
  apply OrdinarySteps.step s (execInstrBr s (.ADDI .x5 .x0 0)) _
    (.base (.ADDI .x5 .x0 0)) 1
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step _ (successState s) _
    (.base (.ADDI .x10 .x0 1)) 0
  · have hp : (execInstrBr s (.ADDI .x5 .x0 0)).pc=0x1d64 := by
      simp [execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  exact OrdinarySteps.refl _

theorem success_pc (s : MachineState) (pc : s.pc=0x1d60) :
    (successState s).pc=0x1d68 := by
  simp [successState,execInstrBr,pc]

theorem finish_success (hash : Hash) (s : MachineState)
    (pc : s.pc=0x1d60) :
    Executes hash image s 3 ⟨.success,successState s,3,0,0⟩ := by
  let final := successState s
  have finalPc : final.pc=0x1d68 := success_pc s pc
  have hf : fetch image final=some (.base .ECALL) := by
    simpa only [Keygen.fetch_at,finalPc] using success_code.2.2
  have hs : final.getReg .x5=0 := by rfl
  have hv : final.getReg .x10=1 := by rfl
  have exec := (success_steps s pc).then_executes
    (Executes.halt (hash := hash) final hf hs)
  simpa [final,hv,Execution.charge] using exec

#print axioms finish_success
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperFinish67
