import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHeader67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHash67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafStore67. -/
section
/-! The direct67 keygen leaf compressor is a real H3 oracle instruction. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem hash_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x13d0)
    (fields : s.getReg .x5 = 1 ∧ s.getReg .x10 = 0x80000 ∧
      s.getReg .x11 = 8832 ∧ s.getReg .x12 = 0x80300) :
    Trace hash image s 1 144 1 18 (writeHash s (hash (hashInput s))) := by
  have code : fetch image s = some (.base .ECALL) := by
    have hc : Keygen.instructionAt image 0x13d0 = some (.base .ECALL) := by
      unfold image GroupedBalancedKeygenImage67.image
      decide
    change Keygen.instructionAt image s.pc = some (.base .ECALL)
    rw [pc]
    exact hc
  obtain ⟨service,source,bits,destination⟩ := fields
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,source,bits,destination,
      accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput s).1 = 8832 := by simp [hashInput,bits]
  simpa [len,compressions] using
    Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

theorem copy_header_hash (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x131c) :
    ∃ final,
      Trace hash image s 844 987 1 18 final ∧
      final.pc = 0x13d4 ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → final.getMem a = s.getMem a) := by
  obtain ⟨copied,first,copiedPC,_,copyFrame⟩ :=
    GroupedBalancedKeygenLeafCopy67.copy_leaf_words s pc
  let ready := GroupedBalancedKeygenLeafHeader67.headerState copied
  have second : Trace hash image copied 34 34 0 0 ready :=
    (GroupedBalancedKeygenLeafHeader67.header_steps copied copiedPC).trace
  have readyPC := GroupedBalancedKeygenLeafHeader67.header_pc copied copiedPC
  have readyRegs := GroupedBalancedKeygenLeafHeader67.header_regs copied
  let final := writeHash ready (hash (hashInput ready))
  have third : Trace hash image ready 1 144 1 18 final :=
    hash_trace hash ready readyPC readyRegs
  refine ⟨final,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd] using (first.trace.trans second).trans third
  · change ready.pc + 4 = 0x13d4
    rw [readyPC]
    decide
  · intro a high
    have copiedHigh : copied.getMem a = s.getMem a := by
      apply copyFrame a
      intro i hi same
      have hn := congrArg BitVec.toNat same
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i < 2^64)] at hn
      omega
    have readyHigh : ready.getMem a = copied.getMem a :=
      GroupedBalancedKeygenLeafHeader67.header_high_frame copied a high
    have finalHigh : final.getMem a = ready.getMem a := by
      apply Signing.hash_answer_frame ready (hash (hashInput ready)) readyRegs.2.2.2 a
      intro i same
      have hn := congrArg BitVec.toNat same
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
      omega
    exact finalHigh.trans (readyHigh.trans copiedHigh)

#print axioms hash_trace
#print axioms copy_header_hash

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafHash67

end

/-! The H3 answer is stored as a leaf and the leaf counter advances. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafStore67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image

private theorem leaf_address (s : MachineState) (n : Nat)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n) :
    (0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4) =
      BitVec.ofNat 64 (0x82000 + 16*n) := by
  rw [counter,KeygenDomain.shift_ofNat]
  simp [BitVec.ofNat_add,Nat.mul_comm]

theorem store_accesses (s : MachineState) (n : Nat)
    (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n) :
    accessValid ((0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4)) 8 = true ∧
    accessValid ((0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4) + 8#64) 8 = true := by
  have addr := leaf_address s n counter
  have addrNext : (0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4) + 8#64 =
      BitVec.ofNat 64 (0x82000+16*n+8) := by
    rw [addr]
    simp [BitVec.ofNat_add]
  constructor
  · rw [addr]
    simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat]
    omega
  · rw [addrNext]
    simp [accessValid,rangeValid,MEMORY_BYTES,BitVec.toNat_ofNat]
    omega
def storeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 130)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 768)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 776)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 16)
  execInstrBr s (.BNE .x6 .x7 7196)
private theorem store_code :
    Keygen.instructionAt image 0x13d4 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x13d8 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x13dc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x13e0 = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x13e4 = some (.base (.LUI .x10 130)) ∧
    Keygen.instructionAt image 0x13e8 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x13ec = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x13f0 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x13f4 = some (.base (.ADDI .x28 .x28 768)) ∧
    Keygen.instructionAt image 0x13f8 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x13fc = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1400 = some (.base (.ADDI .x28 .x28 776)) ∧
    Keygen.instructionAt image 0x1404 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1408 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x140c = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1410 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1414 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1418 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x141c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1420 = some (.base (.ADDI .x7 .x0 16)) ∧
    Keygen.instructionAt image 0x1424 = some (.base (.BNE .x6 .x7 7196))
    := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem store_steps (s : MachineState) (pc : s.pc = 0x13d4)
    (safe : accessValid ((0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4)) 8 = true)
    (safeNext : accessValid ((0x82000#64 : Word) + (s.getMem 0x81008#64 <<< 4) + 8#64) 8 = true) :
    OrdinarySteps image s 21 (storeState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 130)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 0)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 128)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 768)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LUI .x28 128)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 776)
  let s13 := execInstrBr s12 (.LD .x11 .x28 0)
  let s14 := execInstrBr s13 (.SD .x7 .x10 0)
  let s15 := execInstrBr s14 (.SD .x7 .x11 8)
  let s16 := execInstrBr s15 (.ADDI .x6 .x6 1)
  let s17 := execInstrBr s16 (.LUI .x28 129)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 8)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.ADDI .x7 .x0 16)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20⟩ := store_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 20
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s1.pc = 0x13d8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 18
  · have hp : s2.pc = 0x13dc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 17
  · have hp : s3.pc = 0x13e0 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 130)) 16
  · have hp : s4.pc = 0x13e4 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 0)) 15
  · have hp : s5.pc = 0x13e8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x10)) 14
  · have hp : s6.pc = 0x13ec := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 128)) 13
  · have hp : s7.pc = 0x13f0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 768)) 12
  · have hp : s8.pc = 0x13f4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 11
  · have hp : s9.pc = 0x13f8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 128)) 10
  · have hp : s10.pc = 0x13fc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 776)) 9
  · have hp : s11.pc = 0x1400 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x11 .x28 0)) 8
  · have hp : s12.pc = 0x1404 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x7 .x10 0)) 7
  · have hp : s13.pc = 0x1408 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe,safeNext,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [BitVec.add_comm] using safe
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x7 .x11 8)) 6
  · have hp : s14.pc = 0x140c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,safe,safeNext,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [BitVec.add_comm] using safeNext
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s15.pc = 0x1410 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 129)) 4
  · have hp : s16.pc = 0x1414 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 8)) 3
  · have hp : s17.pc = 0x1418 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s18.pc = 0x141c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,storeState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x7 .x0 16)) 1
  · have hp : s19.pc = 0x1420 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 (storeState s) _ (.base (.BNE .x6 .x7 7196)) 0
  · have hp : s20.pc = 0x1424 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  exact OrdinarySteps.refl _

theorem store_pc (s : MachineState) (pc : s.pc = 0x13d4) :
    (storeState s).pc =
      if s.getMem 0x81008#64 + 1 = 16 then 0x1428 else 0x1040 := by
  simp [storeState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem store_mem (s : MachineState) (a : Word) :
    (storeState s).getMem a =
      if a = 0x81008#64 then s.getMem 0x81008#64 + 1 else
      if a = (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 then
        s.getMem 0x80308 else
      if a = (s.getMem 0x81008#64 <<< 4) + 0x82000#64 then
        s.getMem 0x80300 else s.getMem a := by
  simp [storeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

private theorem leaf_address_rev (s : MachineState) (n : Nat)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n) :
    (s.getMem 0x81008#64 <<< 4) + 0x82000#64 =
      BitVec.ofNat 64 (0x82000+16*n) := by
  rw [BitVec.add_comm]
  exact leaf_address s n counter

theorem store_below_frame (s : MachineState) (n : Nat)
    (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n)
    (a : Word) (low : a.toNat < 0x82000) (notCounter : a ≠ 0x81008#64) :
    (storeState s).getMem a = s.getMem a := by
  have addr := leaf_address_rev s n counter
  have next : (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 =
      BitVec.ofNat 64 (0x82000+16*n+8) := by
    rw [addr]
    simp [BitVec.ofNat_add]
  have distinctStart : a ≠ (s.getMem 0x81008#64 <<< 4) + 0x82000#64 := by
    rw [addr]
    intro eq
    have value := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
      (by omega : 0x82000+16*n < 2^64)] at value
    omega
  have distinctNext : a ≠ (s.getMem 0x81008#64 <<< 4) + 0x82000#64 + 8#64 := by
    rw [next]
    intro eq
    have value := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
      (by omega : 0x82000+16*n+8 < 2^64)] at value
    omega
  rw [store_mem,if_neg notCounter,if_neg distinctNext,if_neg distinctStart]

theorem store_counter (s : MachineState) (n : Nat) (bound : n < 16)
    (counter : s.getMem 0x81008#64 = BitVec.ofNat 64 n) :
    (storeState s).getMem 0x81008#64 = BitVec.ofNat 64 (n+1) := by
  rw [store_mem]
  simp only [if_pos rfl,counter]
  simp [BitVec.ofNat_add]

#print axioms store_steps
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafStore67
