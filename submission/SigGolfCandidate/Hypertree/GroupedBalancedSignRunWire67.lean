import SigGolfCandidate.Hypertree.GroupedBalancedSignLoadedWire67

/-! Exact official byte-program signer result for the direct67 signature wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignRunWire67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev byteSubmission := GroupedBalancedProgram67ByteSign.submission

theorem run_refines (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ cycles, cycles ≤ 31914272 ∧
      byteSubmission.runWith hash .sign (secretKey,cache,message) =
        ⟨some (GroupedBalancedWire67.wire
          (GroupedBalancedScheme67.sign hash secretKey message)),
          true,cycles,122548,130710⟩ := by
  obtain ⟨initial,final,steps,cycles,loaded,execution,stepsBound,
    cyclesBound,stored⟩ :=
    GroupedBalancedSignLoadedWire67.loaded_wire
      hash secretKey cache message
  have actual := runWith_of_executes byteSubmission hash .sign
    (secretKey,cache,message) initial steps
    ⟨.success,final,cycles,122548,130710⟩ loaded execution
    (by unfold CYCLE_LIMIT; omega)
  refine ⟨cycles,cyclesBound,?_⟩
  rw [actual]
  change (⟨some (readBuffer final 0x20060 50848),
    true,cycles,122548,130710⟩ : RunResult (Bytes 50848)) = _
  rw [stored]
  rfl

theorem run_resources (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    let result := byteSubmission.runWith hash .sign
      (secretKey,cache,message)
    result.value = some (GroupedBalancedWire67.wire
      (GroupedBalancedScheme67.sign hash secretKey message)) ∧
    result.finished = true ∧ result.cycles ≤ 31914272 ∧
    result.cycles < CYCLE_LIMIT ∧ result.hashCalls = 122548 ∧
    result.hashCompressions = 130710 ∧
    result.hashCompressions < BUDGET_SIGN := by
  obtain ⟨cycles,bound,actual⟩ := run_refines hash secretKey cache message
  dsimp only
  rw [actual]
  dsimp only
  exact ⟨rfl,rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

#print axioms run_refines
#print axioms run_resources
end SigGolfCandidate.Hypertree.GroupedBalancedSignRunWire67
