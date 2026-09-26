import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Tail67

/-! One complete verifier H4 tree round, with control fields for induction. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Round67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem round (hash : Hash) (s : MachineState) (p c : Word)
    (pc : s.pc = 0x1290)
    (pointer : s.getMem 0x81048 = p)
    (count : s.getMem 0x81050 = c)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true) :
    ∃ n final, (n = 162 ∨ n = 163) ∧
      Trace hash image s n (n+7) 1 1 final ∧
      final.getMem 0x81048 = p+16 ∧
      final.getMem 0x81050 = c+1 ∧
      final.pc = (if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      SafeFrame s final := by
  let header := GroupedBalancedVerifyTreeHeader67.headerState s
  have headerRun := GroupedBalancedVerifyTreeHeader67.header_steps s pc
  have headerPC := GroupedBalancedVerifyTreeHeader67.header_pc s pc
  let branch := execInstrBr header (.BEQ .x6 .x0 88)
  have branchRun := GroupedBalancedVerifyTreeHeader67.branch_step header headerPC
  have branchPC := GroupedBalancedVerifyTreeHeader67.branch_pc header headerPC
    (GroupedBalancedVerifyTreeHeader67.header_bit s)
  have branchCases : branch.pc = 0x1314 ∨ branch.pc = 0x1368 := by
    by_cases bit : header.getReg .x6 = 0
    · right
      have bitBV : header.getReg .x6 = 0#64 := by simpa using bit
      simpa [branch,bitBV] using branchPC
    · left
      have bitBV : ¬ header.getReg .x6 = 0#64 := by simpa using bit
      simpa [branch,bitBV] using branchPC
  have branchPointer : branch.getMem 0x81048 = p := by
    simpa [branch,execInstrBr] using
      (GroupedBalancedVerifyTreeHeader67.header_pointer s).trans pointer
  have branchCount : branch.getMem 0x81050 = c := by
    exact (GroupedBalancedVerifyTreeHeader67.branch_count header).trans
      ((GroupedBalancedVerifyTreeHeader67.header_count s).trans count)
  obtain ⟨bn,joined,bnCases,siblingRun,joinedPC,joinedPointer,joinedCount,siblingSafe⟩ :=
    GroupedBalancedVerifyTreeJoin67.sibling_paths branch p branchCases
      branchPointer valid0 valid8
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,copyCount,copySafe⟩ :=
    GroupedBalancedVerifyTreeH4Input67.copy_input joined joinedPC
  let ready := GroupedBalancedVerifyTreeH4Header67.headerState copied
  have header4Run := GroupedBalancedVerifyTreeH4Header67.header_block copied copyPC
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields copied copyPC
  let answered := writeHash ready (hash (hashInput ready))
  have hashRun := GroupedBalancedVerifyTreeH4Query67.hash_trace hash ready fields
  have hashPC := GroupedBalancedVerifyTreeH4Query67.hash_pc hash ready fields
  obtain ⟨stored,answerRun,answerPC,_,answerPointer,answerCount,answerSafe⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.answer_copy answered hashPC
  let final := GroupedBalancedVerifyTreeH4Tail67.updateState stored
  have tailRun := GroupedBalancedVerifyTreeH4Tail67.update_block stored answerPC
  have storedPointer : stored.getMem 0x81048 = p := by
    exact answerPointer.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_pointer hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_pointer copied).trans
          (copyPointer.trans joinedPointer)))
  have storedCount : stored.getMem 0x81050 = c := by
    exact answerCount.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_count hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_count copied).trans
          (copyCount.trans (joinedCount.trans branchCount))))
  refine ⟨136+bn,final,?_,?_,?_,?_,?_,?_⟩
  · rcases bnCases with h | h <;> simp [h]
  · have t0 : Trace hash image s 33 33 0 0 branch :=
      headerRun.trace.trans branchRun.trace
    have t1 := t0.trans siblingRun.trace
    have t2 := t1.trans copyRun.trace
    have t3 := t2.trans header4Run.trace
    have t4 := t3.trans hashRun
    have t5 := t4.trans answerRun.trace
    have all := t5.trans tailRun.trace
    simpa [image,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_pointer,storedPointer]
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_round_count,storedCount]
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_pc_count stored answerPC,storedCount]
  · have h0 := safe_trans
      (GroupedBalancedVerifyTreeHeader67.header_safe s)
      (GroupedBalancedVerifyTreeHeader67.branch_safe header)
    have h1 := safe_trans h0 siblingSafe
    have h2 := safe_trans h1 copySafe
    have h3 := safe_trans h2 (GroupedBalancedVerifyTreeH4Header67.header_safe copied)
    have h4 := safe_trans h3 (GroupedBalancedVerifyTreeH4Query67.hash_safe hash ready fields)
    have h5 := safe_trans h4 answerSafe
    exact safe_trans h5 (GroupedBalancedVerifyTreeH4Tail67.update_safe stored)

#print axioms round
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Round67
