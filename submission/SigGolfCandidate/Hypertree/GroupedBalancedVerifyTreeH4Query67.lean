import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Header67

/-! The first verifier H4 node query. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem query_code : Keygen.instructionAt image 0x1468 = some (.base .ECALL) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

structure Fields (s : MachineState) : Prop where
  pc : s.pc = 0x1468
  source : s.getReg .x10 = 0x80000
  bits : s.getReg .x11 = 512
  destination : s.getReg .x12 = 0x80300
  service : s.getReg .x5 = 1

theorem header_fields (s : MachineState) (pc : s.pc = 0x13e4) :
    Fields (GroupedBalancedVerifyTreeH4Header67.headerState s) := by
  constructor
  · exact GroupedBalancedVerifyTreeH4Header67.header_pc s pc
  · simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [GroupedBalancedVerifyTreeH4Header67.headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem hash_trace (hash : Hash) (s : MachineState) (fields : Fields s) :
    Trace hash image s 1 8 1 1 (writeHash s (hash (hashInput s))) := by
  have fetched : fetch image s = some (.base .ECALL) := by
    simpa only [Keygen.fetch_at,fields.pc] using query_code
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,fields.source,fields.bits,
      fields.destination,accessValid,rangeValid,MEMORY_BYTES]
  have bits : (hashInput s).1 = 512 := by simp [hashInput,fields.bits]
  simpa [bits,compressions] using
    Trace.hash s _ 0 0 0 0 fetched fields.service valid (Trace.refl _)

theorem hash_pc (hash : Hash) (s : MachineState) (fields : Fields s) :
    (writeHash s (hash (hashInput s))).pc = 0x146c := by
  simp [writeHash,fields.pc]

theorem hash_pointer (hash : Hash) (s : MachineState) (fields : Fields s) :
    (writeHash s (hash (hashInput s))).getMem 0x81048 = s.getMem 0x81048 := by
  simp [writeHash,fields.destination]

theorem hash_count (hash : Hash) (s : MachineState) (fields : Fields s) :
    (writeHash s (hash (hashInput s))).getMem 0x81050 = s.getMem 0x81050 := by
  simp [writeHash,fields.destination]

theorem hash_safe (hash : Hash) (s : MachineState) (fields : Fields s) :
    GroupedBalancedVerifyTreeHighFrame67.SafeFrame s
      (writeHash s (hash (hashInput s))) := by
  constructor
  · intro a ha
    simp [writeHash,fields.destination]
    split_ifs with e1 e2 e3 e4
    all_goals
      try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
      try rfl
  · simp [writeHash,MachineState.getReg_setReg_ne]

theorem loaded_hash (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n final,
      initialState program .verify input = some initial ∧
      (n = 340 ∨ n = 341) ∧
      Trace hash image initial n (n+29) 3 4 final ∧
      final.pc = 0x146c ∧ final.getMem 0x81048 = 0x2c730 := by
  obtain ⟨initial,n,before,loaded,ncases,beforeRun,beforePC,pointer⟩ :=
    GroupedBalancedVerifyTreeH4Input67.loaded_input hash input
  let ready := GroupedBalancedVerifyTreeH4Header67.headerState before
  have headerRun := GroupedBalancedVerifyTreeH4Header67.header_block before beforePC
  have fields := header_fields before beforePC
  let final := writeHash ready (hash (hashInput ready))
  have hashRun := hash_trace hash ready fields
  refine ⟨initial,n+34,final,loaded,?_,?_,hash_pc hash ready fields,?_⟩
  · rcases ncases with h | h <;> simp [h]
  · have run := (beforeRun.trans headerRun.trace).trans hashRun
    simpa [image,final,ready,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run
  · exact (hash_pointer hash ready fields).trans
      ((GroupedBalancedVerifyTreeH4Header67.header_pointer before).trans pointer)

#print axioms hash_trace
#print axioms loaded_hash
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Query67
