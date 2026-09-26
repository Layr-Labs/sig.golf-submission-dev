import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHeader67

/-! The first H4 tree round reaches one of the two sibling-order paths. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeBranch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

theorem loaded_branch (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 251 273 2 3 final ∧
      (final.pc = 0x1314 ∨ final.pc = 0x1368) ∧
      final.getMem 0x81048 = 0x2c730 := by
  obtain ⟨initial,ready,loaded,beforeTrace,readyPC,pointer,_⟩ :=
    GroupedBalancedVerifyTreeStart67.loaded_start hash input
  let header := GroupedBalancedVerifyTreeHeader67.headerState ready
  have headerRun := GroupedBalancedVerifyTreeHeader67.header_steps ready readyPC
  have headerPC := GroupedBalancedVerifyTreeHeader67.header_pc ready readyPC
  let final := execInstrBr header (.BEQ .x6 .x0 88)
  have branchRun := GroupedBalancedVerifyTreeHeader67.branch_step header headerPC
  have branchPC := GroupedBalancedVerifyTreeHeader67.branch_pc header headerPC
    (GroupedBalancedVerifyTreeHeader67.header_bit ready)
  refine ⟨initial,final,loaded,?_,?_,?_⟩
  · have composed := beforeTrace.trans (headerRun.trace.trans branchRun.trace)
    simpa only [Nat.reduceAdd] using composed
  · by_cases bit : header.getReg .x6 = 0
    · right
      have bitBV : header.getReg .x6 = 0#64 := by simpa using bit
      simpa [final,bitBV] using branchPC
    · left
      have bitBV : ¬ header.getReg .x6 = 0#64 := by simpa using bit
      simpa [final,bitBV] using branchPC
  · simpa [final,execInstrBr,header] using
      (GroupedBalancedVerifyTreeHeader67.header_pointer ready).trans pointer

#print axioms loaded_branch
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeBranch67
