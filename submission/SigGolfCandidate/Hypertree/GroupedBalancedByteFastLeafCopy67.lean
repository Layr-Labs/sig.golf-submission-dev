import SigGolfCandidate.Hypertree.GroupedBalancedByteFastIteration67


/-! The direct67 upper-leaf compression query in the Fast2Byte verifier. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem query_code :
    Keygen.instructionAt image 0x1718 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

structure Fields (s : MachineState) : Prop where
  pc : s.pc = 0x1718
  source : s.getReg .x10 = 0x80000
  bits : s.getReg .x11 = 8832
  destination : s.getReg .x12 = 0x80300
  service : s.getReg .x5 = 1

theorem hash_input_bits (s : MachineState) (fields : Fields s) :
    (hashInput s).1 = 8832 := by
  simp [hashInput, fields.bits]

theorem hash_valid (s : MachineState) (fields : Fields s) :
    hashArgumentsValid s = true := by
  simp [hashArgumentsValid, fields.source, fields.bits,
    fields.destination, accessValid, rangeValid, MEMORY_BYTES]

theorem hash_trace (hash : Hash) (s : MachineState) (fields : Fields s) :
    Trace hash image s 1 144 1 18
      (writeHash s (hash (hashInput s))) := by
  have fetched : fetch image s = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at, fields.pc] using query_code
  have valid := hash_valid s fields
  have bits := hash_input_bits s fields
  simpa [bits, compressions] using
    Trace.hash s _ 0 0 0 0 fetched fields.service valid (Trace.refl _)

theorem hash_pc (hash : Hash) (s : MachineState) (fields : Fields s) :
    (writeHash s (hash (hashInput s))).pc = 0x171c := by
  simp [writeHash, fields.pc]

theorem hash_reg (hash : Hash) (s : MachineState) (r : Reg) :
    (writeHash s (hash (hashInput s))).getReg r = s.getReg r := by
  simp [writeHash, MachineState.writeWords]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQuery67


/-! The two-word upper-leaf digest copy after the 18-block hash. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQuery67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def SetupCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x171c = some (.base (.LUI .x6 0x80)) ∧
  Keygen.instructionAt image 0x1720 = some (.base (.ADDI .x6 .x6 0x300)) ∧
  Keygen.instructionAt image 0x1724 = some (.base (.LUI .x7 0x80)) ∧
  Keygen.instructionAt image 0x1728 = some (.base (.ADDI .x7 .x7 0x500)) ∧
  Keygen.instructionAt image 0x172c = some (.base (.ADDI .x10 .x0 2))

theorem setup_code : SetupCode image := by
  unfold SetupCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x500)
  execInstrBr s (.ADDI .x10 .x0 2)

theorem setup_block (s : MachineState) (pc : s.pc = 0x171c) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x500)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x1720 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = 0x1724 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x500)) 1
  · have hp : s3.pc = 0x1728 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 _ _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x172c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_fields (s : MachineState) (pc : s.pc = 0x171c) :
    (setupState s).pc = 0x1730 ∧
    (setupState s).getReg .x6 = 0x80300 ∧
    (setupState s).getReg .x7 = 0x80500 ∧
    (setupState s).getReg .x10 = 2 := by
  simp [setupState,execInstrBr,pc,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x1730 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image Keygen.CopyCode
  decide

theorem tail_code :
    Keygen.instructionAt image 0x1748 =
      some (.base (.ADDI .x6 .x0 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def copyState (s : MachineState) : MachineState :=
  let prepared := setupState s
  let first := Expansion.loopNext prepared
  let second := Expansion.loopNext first
  execInstrBr second (.ADDI .x6 .x0 0)

theorem copy_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x171c) :
    Trace hash image s 18 18 0 0 (copyState s) := by
  let prepared := setupState s
  let first := Expansion.loopNext prepared
  let second := Expansion.loopNext first
  obtain ⟨preparedPC,preparedSrc,preparedDst,preparedCount⟩ := setup_fields s pc
  have pre := setup_block s pc
  have firstBlock := Keygen.copy_block image 0x1730 copy_code prepared
    preparedPC (by change accessValid ((setupState s).getReg .x6) 8 = true
                   rw [preparedSrc]; decide)
    (by change accessValid ((setupState s).getReg .x7) 8 = true
        rw [preparedDst]; decide)
  have firstPC : first.pc = 0x1730 := by
    rw [show first = Expansion.loopNext prepared by rfl,
      Keygen.copy_next_pc,preparedCount,preparedPC]
    decide
  have firstRegs := Expansion.loop_next_regs prepared
  have secondSrc : first.getReg .x6 = 0x80308 := by
    rw [firstRegs.1,preparedSrc]
    decide
  have secondDst : first.getReg .x7 = 0x80508 := by
    rw [firstRegs.2.1,preparedDst]
    decide
  have secondCount : first.getReg .x10 = 1 := by
    rw [firstRegs.2.2,preparedCount]
    decide
  have secondBlock := Keygen.copy_block image 0x1730 copy_code first
    firstPC (by rw [secondSrc]; decide)
    (by rw [secondDst]; decide)
  have secondPC : second.pc = 0x1748 := by
    rw [show second = Expansion.loopNext first by rfl,
      Keygen.copy_next_pc,secondCount,firstPC]
    decide
  have tail : OrdinarySteps image second 1
      (execInstrBr second (.ADDI .x6 .x0 0)) := by
    apply OrdinarySteps.step second _ _ (.base (.ADDI .x6 .x0 0)) 0
    · simpa only [Keygen.fetch_at,secondPC] using tail_code
    · rfl
    exact OrdinarySteps.refl _
  have whole : Trace hash image s (5 + (6 + (6 + 1)))
      (5 + (6 + (6 + 1))) 0 0
      (execInstrBr second (.ADDI .x6 .x0 0)) :=
    (OrdinarySteps.trace (hash := hash) pre).trans
      ((OrdinarySteps.trace (hash := hash) firstBlock).trans
        ((OrdinarySteps.trace (hash := hash) secondBlock).trans
          (OrdinarySteps.trace (hash := hash) tail)))
  simpa [copyState,prepared,first,second] using whole

theorem copy_mem (s : MachineState) (pc : s.pc = 0x171c)
    (a : Word) :
    (copyState s).getMem a =
      if a = 0x80508 then s.getMem 0x80308
      else if a = 0x80500 then s.getMem 0x80300
      else s.getMem a := by
  let prepared := setupState s
  let first := Expansion.loopNext prepared
  obtain ⟨_,source,dest,_⟩ := setup_fields s pc
  have source1 : first.getReg .x6 = 0x80308 := by
    rw [(Expansion.loop_next_regs prepared).1, source]
    decide
  have dest1 : first.getReg .x7 = 0x80508 := by
    rw [(Expansion.loop_next_regs prepared).2.1, dest]
    decide
  have firstMem (b : Word) :
      first.getMem b =
        if b = 0x80500 then s.getMem 0x80300 else s.getMem b := by
    change (Expansion.loopNext prepared).getMem b = _
    rw [Expansion.loop_next_mem, dest, source]
    split_ifs <;> exact setup_mem s _
  change (execInstrBr (Expansion.loopNext first) (.ADDI .x6 .x0 0)).getMem a = _
  rw [show (execInstrBr (Expansion.loopNext first) (.ADDI .x6 .x0 0)).getMem a =
    (Expansion.loopNext first).getMem a by simp [execInstrBr]]
  rw [Expansion.loop_next_mem, dest1, source1,
    firstMem 0x80308, firstMem a]
  simp

theorem copy_pc (s : MachineState) (pc : s.pc = 0x171c) :
    (copyState s).pc = 0x174c := by
  let prepared := setupState s
  let first := Expansion.loopNext prepared
  let second := Expansion.loopNext first
  have fields := setup_fields s pc
  have firstPC : first.pc = 0x1730 := by
    rw [show first = Expansion.loopNext prepared by rfl,
      Keygen.copy_next_pc,fields.2.2.2,fields.1]
    decide
  have firstCount : first.getReg .x10 = 1 := by
    rw [show first = Expansion.loopNext prepared by rfl,
      (Expansion.loop_next_regs prepared).2.2,fields.2.2.2]
    decide
  have secondPC : second.pc = 0x1748 := by
    rw [show second = Expansion.loopNext first by rfl,
      Keygen.copy_next_pc,firstCount,firstPC]
    decide
  change (execInstrBr second (.ADDI .x6 .x0 0)).pc = 0x174c
  simp [execInstrBr,secondPC]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCopy67
