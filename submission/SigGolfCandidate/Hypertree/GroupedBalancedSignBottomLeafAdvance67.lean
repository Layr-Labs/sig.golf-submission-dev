import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstH267


/-! The first four loaded signer hash calls reach the first bottom leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH267
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

theorem loaded_first_bottom_leaf (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial h1After ready after : MachineState,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial
        (if h1After.getMem 0x810e0 = h1After.getMem 0x810e8 then 430 else 413)
        (if h1After.getMem 0x810e0 = h1After.getMem 0x810e8 then 474 else 457)
        4 6 after ∧
      ready.pc = 0x1474 ∧ after.pc = 0x1478 ∧
      hashInput ready = Reference.packed (KeygenDomain.payload
        (KeygenDomain.header 2 0 0 0 0)
        (leafIndex (Reference.indexOf hash message
          (Reference.randomizer hash secretKey message)))
        (GroupedBottomTree.secret hash secretKey
          (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message))))) ∧
      (∀ i : Fin 2, after.getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.leafRoot hash secretKey
          (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)))).extractLsb'
              (64*i.val) 64) := by
  obtain ⟨initial,h1Ready,h1After,loaded,h1,h1ReadyPc,h1AfterPc,
    h1Query,seedWords,level,address,_⟩ :=
    GroupedBalancedSignBottomLoadedH167.loaded_first_bottom_secret
      hash secretKey cache message
  let leaf := leafIndex (Reference.indexOf hash message
    (Reference.randomizer hash secretKey message))
  let seed := GroupedBottomTree.secret hash secretKey leaf
  obtain ⟨ready,after,h2,readyPc,afterPc,query,leafWords,_,_,_⟩ :=
    GroupedBalancedSignBottomFirstH267.first_leaf_h2 hash h1After
      leaf seed h1AfterPc level address seedWords
  refine ⟨initial,h1After,ready,after,loaded,?_,readyPc,afterPc,query,?_⟩
  · by_cases selected : h1After.getMem 0x810e0 = h1After.getMem 0x810e8
    · simp only [if_pos selected] at h2 ⊢
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        h1.trans h2
    · simp only [if_neg selected] at h2 ⊢
      simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        h1.trans h2
  · intro i
    simpa only [leaf,seed,GroupedBottomTree.leafRoot] using leafWords i

#print axioms loaded_first_bottom_leaf
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH267


/-! Store one bottom leaf value and advance the leaf/address counters. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 0x83)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x300)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 8)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 1024)
  execInstrBr s (.BNE .x6 .x7 (-540))

private theorem advance_code :
    Keygen.instructionAt image 0x1478 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x147c = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x1480 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1484 = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x1488 = some (.base (.LUI .x10 0x83)) ∧
    Keygen.instructionAt image 0x148c = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1490 = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x1494 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1498 = some (.base (.ADDI .x28 .x28 0x300)) ∧
    Keygen.instructionAt image 0x149c = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x14a0 = some (.base (.LD .x11 .x28 8)) ∧
    Keygen.instructionAt image 0x14a4 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x14a8 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x14ac = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14b0 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x14b4 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x14b8 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x14bc = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14c0 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x14c4 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x14c8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14cc = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x14d0 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x14d4 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x14d8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14dc = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x14e0 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x14e4 = some (.base (.ADDI .x7 .x0 1024)) ∧
    Keygen.instructionAt image 0x14e8 = some (.base (.BNE .x6 .x7 (-540))) := by
  decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x1478)
    (valid : accessValid ((s.getMem 0x810e0 <<< 4) + 0x83000) 8 = true)
    (valid8 : accessValid ((s.getMem 0x810e0 <<< 4) + 0x83000 + 8) 8 = true) :
    OrdinarySteps image s 29 (advanceState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xe0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 0x83)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 0)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 0x80)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0x300)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LD .x11 .x28 8)
  let s12 := execInstrBr s11 (.SD .x7 .x10 0)
  let s13 := execInstrBr s12 (.SD .x7 .x11 8)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 8)
  let s16 := execInstrBr s15 (.LD .x6 .x28 0)
  let s17 := execInstrBr s16 (.ADDI .x6 .x6 1)
  let s18 := execInstrBr s17 (.LUI .x28 0x81)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 8)
  let s20 := execInstrBr s19 (.SD .x28 .x6 0)
  let s21 := execInstrBr s20 (.LUI .x28 0x81)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 0xe0)
  let s23 := execInstrBr s22 (.LD .x6 .x28 0)
  let s24 := execInstrBr s23 (.ADDI .x6 .x6 1)
  let s25 := execInstrBr s24 (.LUI .x28 0x81)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 0xe0)
  let s27 := execInstrBr s26 (.SD .x28 .x6 0)
  let s28 := execInstrBr s27 (.ADDI .x7 .x0 1024)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 28
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xe0)) 27
  · have hp : s1.pc = 0x147c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 26
  · have hp : s2.pc = 0x1480 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 25
  · have hp : s3.pc = 0x1484 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 0x83)) 24
  · have hp : s4.pc = 0x1488 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 0)) 23
  · have hp : s5.pc = 0x148c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x10)) 22
  · have hp : s6.pc = 0x1490 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x80)) 21
  · have hp : s7.pc = 0x1494 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0x300)) 20
  · have hp : s8.pc = 0x1498 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 19
  · have hp : s9.pc = 0x149c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x11 .x28 8)) 18
  · have hp : s10.pc = 0x14a0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  have stackReg : s11.getReg .x7 =
      (s.getMem 0x810e0 <<< 4) + 0x83000 := by
    simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,BitVec.add_comm]
  have validS11 : accessValid (s11.getReg .x7) 8 = true := by
    rw [stackReg]
    exact valid
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x7 .x10 0)) 17
  · have hp : s11.pc = 0x14a4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s12,ordinaryStep,memoryArgumentsValid,signExtend12,validS11]
  have validS12 : accessValid (s12.getReg .x7 + 8) 8 = true := by
    simpa [s12,execInstrBr,stackReg] using valid8
  have validS12' : accessValid (s12.getReg .x7 + signExtend12 (8 : BitVec 12)) 8 = true := by
    simpa [signExtend12] using validS12
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x7 .x11 8)) 16
  · have hp : s12.pc = 0x14a8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp only [ordinaryStep,memoryArgumentsValid]
    exact if_pos validS12'
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 15
  · have hp : s13.pc = 0x14ac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 8)) 14
  · have hp : s14.pc = 0x14b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.LD .x6 .x28 0)) 13
  · have hp : s15.pc = 0x14b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x6 .x6 1)) 12
  · have hp : s16.pc = 0x14b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s17.pc = 0x14bc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 8)) 10
  · have hp : s18.pc = 0x14c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s19.pc = 0x14c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s20.pc = 0x14c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 0xe0)) 7
  · have hp : s21.pc = 0x14cc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x6 .x28 0)) 6
  · have hp : s22.pc = 0x14d0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s23.pc = 0x14d4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x81)) 4
  · have hp : s24.pc = 0x14d8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 0xe0)) 3
  · have hp : s25.pc = 0x14dc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s26.pc = 0x14e0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x7 .x0 1024)) 1
  · have hp : s27.pc = 0x14e4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 (advanceState s) _ (.base (.BNE .x6 .x7 (-540))) 0
  · have hp : s28.pc = 0x14e8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  exact OrdinarySteps.refl _

#print axioms advance_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafAdvance67
