import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeaf67


/-! The one-block Merkle-node query in each Fast2Byte upper edge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem query_code :
    Keygen.instructionAt image 0x1930 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

structure Fields (s : MachineState) : Prop where
  pc : s.pc = 0x1930
  source : s.getReg .x10 = 0x80000
  bits : s.getReg .x11 = 512
  destination : s.getReg .x12 = 0x80300
  service : s.getReg .x5 = 1

theorem hash_trace (hash : Hash) (s : MachineState) (fields : Fields s) :
    Trace hash image s 1 8 1 1
      (writeHash s (hash (hashInput s))) := by
  have fetched : fetch image s = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at,fields.pc] using query_code
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,fields.source,fields.bits,
      fields.destination,accessValid,rangeValid,MEMORY_BYTES]
  have bits : (hashInput s).1 = 512 := by simp [hashInput,fields.bits]
  simpa [bits,compressions] using
    Trace.hash s _ 0 0 0 0 fetched fields.service valid (Trace.refl _)

theorem hash_pc (hash : Hash) (s : MachineState) (fields : Fields s) :
    (writeHash s (hash (hashInput s))).pc = 0x1934 := by
  simp [writeHash,fields.pc]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeQuery67


/-! Four repeated word-copy loops of the Fast2Byte upper Merkle path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def SetupCode (image : Image) (p : Word)
    (src dst count : BitVec 12) : Prop :=
  Keygen.instructionAt image p = some (.base (.LUI .x6 0x80)) ∧
  Keygen.instructionAt image (p+4) = some (.base (.ADDI .x6 .x6 src)) ∧
  Keygen.instructionAt image (p+8) = some (.base (.LUI .x7 0x80)) ∧
  Keygen.instructionAt image (p+12) = some (.base (.ADDI .x7 .x7 dst)) ∧
  Keygen.instructionAt image (p+16) = some (.base (.ADDI .x10 .x0 count))

def setupState (s : MachineState) (src dst count : BitVec 12) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 src)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 dst)
  execInstrBr s (.ADDI .x10 .x0 count)

theorem setup_block (p : Word) (src dst count : BitVec 12)
    (code : SetupCode image p src dst count)
    (s : MachineState) (pc : s.pc = p) :
    OrdinarySteps image s 5 (setupState s src dst count) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 src)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 dst)
  obtain ⟨c0,c1,c2,c3,c4⟩ := code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 src)) 3
  · have hp : s1.pc = p+4 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s2.pc = p+8 := by simp [s1,s2,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 dst)) 1
  · have hp : s3.pc = p+12 := by
      simp [s1,s2,s3,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 _ _ (.base (.ADDI .x10 .x0 count)) 0
  · have hp : s4.pc = p+16 := by
      simp [s1,s2,s3,s4,execInstrBr,pc,BitVec.add_assoc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (src dst count : BitVec 12) :
    (setupState s src dst count).pc = s.pc + 20 := by
  simp [setupState,execInstrBr,BitVec.add_assoc]

theorem witness_copy_code :
    SetupCode image 0x17dc 0x500 0x530 2 ∧
    Keygen.CopyCode image 0x17f0 := by
  unfold SetupCode Keygen.CopyCode image
    GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem sibling_copy_code :
    SetupCode image 0x1830 0x500 0x520 2 ∧
    Keygen.CopyCode image 0x1844 := by
  unfold SetupCode Keygen.CopyCode image
    GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem child_copy_code :
    SetupCode image 0x1880 0x520 0x020 4 ∧
    Keygen.CopyCode image 0x1894 := by
  unfold SetupCode Keygen.CopyCode image
    GroupedBalancedVerifyImage67Fast2Byte.image
  decide

theorem result_copy_code :
    SetupCode image 0x1934 0x300 0x500 2 ∧
    Keygen.CopyCode image 0x1948 := by
  unfold SetupCode Keygen.CopyCode image
    GroupedBalancedVerifyImage67Fast2Byte.image
  decide

/-- The generic five-instruction setup plus the organizer's exact six-step
copy loop. This exposes all pointer and counter fields at the exit. -/
theorem run_copy (hash : Hash) (s : MachineState)
    (p : Word) (src dst count : BitVec 12)
    (source destination total : Nat)
    (setup : SetupCode image p src dst count)
    (loop : Keygen.CopyCode image (p+20))
    (pc : s.pc = p)
    (sourceReg : (setupState s src dst count).getReg .x6 =
      BitVec.ofNat 64 source)
    (destinationReg : (setupState s src dst count).getReg .x7 =
      BitVec.ofNat 64 destination)
    (countReg : (setupState s src dst count).getReg .x10 =
      BitVec.ofNat 64 total)
    (positive : 0 < total)
    (size : total ≤ 2097152)
    (sourceBound : source + 8 * total ≤ MEMORY_BYTES)
    (destinationBound : destination + 8 * total ≤ MEMORY_BYTES)
    (sourceAlign : source % 8 = 0)
    (destinationAlign : destination % 8 = 0) :
    ∃ final, Trace hash image s (5 + 6 * total)
        (5 + 6 * total) 0 0 final ∧
      Keygen.CopyInvariant (p+20) source destination total 0 final := by
  let prepared := setupState s src dst count
  have first := setup_block p src dst count setup s pc
  have inv : Keygen.CopyInvariant (p+20) source destination total total
      prepared := by
    refine ⟨Nat.le_refl _, size, ?_, ?_, ?_, countReg⟩
    · simp [positive.ne',prepared,setup_pc,pc]
    · simpa using sourceReg
    · simpa using destinationReg
  obtain ⟨final, second, done⟩ := Keygen.copy_loop image (p+20)
    loop source destination total total prepared inv
      sourceBound destinationBound sourceAlign destinationAlign
  refine ⟨final, ?_, done⟩
  have trace := (OrdinarySteps.trace (hash := hash) first).trans
    (OrdinarySteps.trace (hash := hash) second)
  simpa [prepared,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using trace

theorem setup_reg (s : MachineState)
    (src dst count : BitVec 12) (r : Reg) :
    (setupState s src dst count).getReg r =
      (if r = .x10 then (signExtend12 count)
       else if r = .x7 then (0x80000 : Word) + signExtend12 dst
       else if r = .x6 then (0x80000 : Word) + signExtend12 src
       else s.getReg r) := by
  cases r <;> simp [setupState,execInstrBr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem child_copy (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1880) :
    ∃ final, Trace hash image s 29 29 0 0 final ∧
      Keygen.CopyInvariant 0x1894 0x80520 0x80020 4 0 final := by
  obtain ⟨final, trace, inv⟩ := run_copy hash s
    0x1880 0x520 0x020 4 0x80520 0x80020 4
    child_copy_code.1 child_copy_code.2 pc
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨final, by simpa using trace, by simpa using inv⟩

theorem result_copy (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1934) :
    ∃ final, Trace hash image s 17 17 0 0 final ∧
      Keygen.CopyInvariant 0x1948 0x80300 0x80500 2 0 final := by
  obtain ⟨final, trace, inv⟩ := run_copy hash s
    0x1934 0x300 0x500 2 0x80300 0x80500 2
    result_copy_code.1 result_copy_code.2 pc
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨final, by simpa using trace, by simpa using inv⟩

theorem witness_copy (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x17dc) :
    ∃ final, Trace hash image s 17 17 0 0 final ∧
      Keygen.CopyInvariant 0x17f0 0x80500 0x80530 2 0 final := by
  obtain ⟨final, trace, inv⟩ := run_copy hash s
    0x17dc 0x500 0x530 2 0x80500 0x80530 2
    witness_copy_code.1 witness_copy_code.2 pc
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨final, by simpa using trace, by simpa using inv⟩

theorem sibling_copy (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1830) :
    ∃ final, Trace hash image s 17 17 0 0 final ∧
      Keygen.CopyInvariant 0x1844 0x80500 0x80520 2 0 final := by
  obtain ⟨final, trace, inv⟩ := run_copy hash s
    0x1830 0x500 0x520 2 0x80500 0x80520 2
    sibling_copy_code.1 sibling_copy_code.2 pc
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by simp [setup_reg,signExtend12])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨final, by simpa using trace, by simpa using inv⟩

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67
