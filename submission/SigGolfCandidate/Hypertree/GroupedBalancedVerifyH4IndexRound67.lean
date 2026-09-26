import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexSibling67

/-! One full H4 round advances the scratch index by one logical right shift. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexRound67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
open GroupedBalancedVerifyH4IndexHeader67
open GroupedBalancedVerifyH4IndexFrame67
open GroupedBalancedVerifyH4IndexSibling67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem round_index (hash : Hash) (s : MachineState) (p c : Word)
    (index : BitVec 192)
    (pc : s.pc = 0x1290)
    (pointer : s.getMem 0x81048 = p)
    (count : s.getMem 0x81050 = c)
    (valid0 : accessValid p 8 = true)
    (valid8 : accessValid (p+8) 8 = true)
    (stored : StoredIndex s index) :
    ∃ n final, (n = 162 ∨ n = 163) ∧
      Trace hash image s n (n+7) 1 1 final ∧
      final.getMem 0x81048 = p+16 ∧
      final.getMem 0x81050 = c+1 ∧
      final.pc = (if c+1 ≠ (10 : Word) then 0x1290 else 0x14f4) ∧
      SafeFrame s final ∧ StoredIndex final (index >>> 1) ∧
      final.getMem 0x81000 = s.getMem 0x81000 + 1 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame s final := by
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
  have branchBase : branch.getMem 0x81000 = s.getMem 0x81000 := by
    have h0 : branch.getMem 0x81000 = header.getMem 0x81000 := by
      simp [branch,execInstrBr]
    exact h0.trans (GroupedBalancedVerifyTreeH4Base67.header_base s)
  obtain ⟨bn,joined,bnCases,siblingRun,joinedPC,joinedPointer,
    joinedCount,siblingSafe,siblingIndex,joinedBase,joinedLow⟩ :=
    sibling_paths_index branch p branchCases branchPointer valid0 valid8
  obtain ⟨copied,copyRun,copyPC,_,copyPointer,copyCount,copySafe⟩ :=
    GroupedBalancedVerifyTreeH4Input67.copy_input joined joinedPC
  let ready := GroupedBalancedVerifyTreeH4Header67.headerState copied
  have header4Run := GroupedBalancedVerifyTreeH4Header67.header_block copied copyPC
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields copied copyPC
  let answered := writeHash ready (hash (hashInput ready))
  have hashRun := GroupedBalancedVerifyTreeH4Query67.hash_trace hash ready fields
  have hashPC := GroupedBalancedVerifyTreeH4Query67.hash_pc hash ready fields
  obtain ⟨storedAnswer,answerRun,answerPC,_,answerPointer,
    answerCount,answerSafe⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.answer_copy answered hashPC
  let final := GroupedBalancedVerifyTreeH4Tail67.updateState storedAnswer
  have tailRun := GroupedBalancedVerifyTreeH4Tail67.update_block storedAnswer answerPC
  have storedPointer : storedAnswer.getMem 0x81048 = p := by
    exact answerPointer.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_pointer hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_pointer copied).trans
          (copyPointer.trans joinedPointer)))
  have storedCount : storedAnswer.getMem 0x81050 = c := by
    exact answerCount.trans
      ((GroupedBalancedVerifyTreeH4Query67.hash_count hash ready fields).trans
        ((GroupedBalancedVerifyTreeH4Header67.header_count copied).trans
          (copyCount.trans (joinedCount.trans branchCount))))
  have storedBase : storedAnswer.getMem 0x81000 = s.getMem 0x81000 := by
    have h0 := GroupedBalancedVerifyTreeH4Base67.answer_copy_base
      answered storedAnswer hashPC answerRun
    have h1 := GroupedBalancedVerifyTreeH4Base67.hash_base ready
      (hash (hashInput ready)) fields.destination
    have h2 := GroupedBalancedVerifyTreeH4Base67.h4_header_base copied
    have h3 := GroupedBalancedVerifyTreeH4Base67.input_copy_base
      joined copied joinedPC copyRun
    exact h0.trans (h1.trans (h2.trans
      (h3.trans (joinedBase.trans branchBase))))
  refine ⟨136+bn,final,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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
  · rw [GroupedBalancedVerifyTreeH4Tail67.update_pc_count storedAnswer
      answerPC,storedCount]
  · have h0 := safe_trans
      (GroupedBalancedVerifyTreeHeader67.header_safe s)
      (GroupedBalancedVerifyTreeHeader67.branch_safe header)
    have h1 := safe_trans h0 siblingSafe
    have h2 := safe_trans h1 copySafe
    have h3 := safe_trans h2
      (GroupedBalancedVerifyTreeH4Header67.header_safe copied)
    have h4 := safe_trans h3
      (GroupedBalancedVerifyTreeH4Query67.hash_safe hash ready fields)
    have h5 := safe_trans h4 answerSafe
    exact safe_trans h5
      (GroupedBalancedVerifyTreeH4Tail67.update_safe storedAnswer)
  · have frame : IndexFrame header final := by
      have h0 := index_trans (branch_index header) siblingIndex
      have h1 := index_trans h0 (input_copy_index joined copied joinedPC copyRun)
      have h2 := index_trans h1 (h4_header_index copied)
      have h3 := index_trans h2 (hash_index hash ready fields)
      have h4 := index_trans h3
        (answer_copy_index answered storedAnswer hashPC answerRun)
      exact index_trans h4 (tail_index storedAnswer)
    exact stored_of_frame frame (header_refines s index stored)
  · rw [GroupedBalancedVerifyTreeH4Base67.tail_base,storedBase]
  · have h0 := (GroupedBalancedVerifyTreeH4Base67.header_low s).trans
      (GroupedBalancedVerifyTreeH4Base67.branch_low header)
    have h1 := h0.trans joinedLow
    have h2 := h1.trans
      (GroupedBalancedVerifyTreeH4Base67.input_copy_low
        joined copied joinedPC copyRun)
    have h3 := h2.trans
      (GroupedBalancedVerifyTreeH4Base67.h4_header_low copied)
    have h4 := h3.trans
      (GroupedBalancedVerifyTreePrefixSafe67.hash_low ready
        (hash (hashInput ready)) fields.destination)
    have h5 := h4.trans
      (GroupedBalancedVerifyTreeH4Base67.answer_copy_low
        answered storedAnswer hashPC answerRun)
    exact h5.trans (GroupedBalancedVerifyTreeH4Base67.tail_low storedAnswer)

#print axioms round_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexRound67
