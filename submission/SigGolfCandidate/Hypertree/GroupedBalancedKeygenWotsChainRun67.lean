import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelector67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstInput67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelectorAll67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67. -/
section
/-! General WOTS radix selector branches for every chain index. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelectorAll67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev normal := GroupedBalancedKeygenWotsSelector67.selectorState

private theorem normal_code :
    Keygen.instructionAt image 0x127c = some (.base (.ADDI .x7 .x0 3)) ∧
    Keygen.instructionAt image 0x1280 = some (.base (.ADDI .x10 .x0 65)) ∧
    Keygen.instructionAt image 0x1284 = some (.base (.BEQ .x19 .x10 16)) ∧
    Keygen.instructionAt image 0x1288 = some (.base (.ADDI .x10 .x0 66)) ∧
    Keygen.instructionAt image 0x128c = some (.base (.BEQ .x19 .x10 16)) ∧
    Keygen.instructionAt image 0x1290 = some (.base (.JAL .x0 16)) ∧
    Keygen.instructionAt image 0x12a0 = some (.base (.ADD .x20 .x7 .x0)) ∧
    Keygen.instructionAt image 0x12a4 = some (.base (.ADDI .x21 .x0 0)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem normal_steps (s : MachineState) (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64) (not66 : s.getReg .x19 ≠ 66#64) :
    OrdinarySteps image s 8 (normal s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 3)
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 65)
  let s3 := execInstrBr s2 (.BEQ .x19 .x10 16)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 66)
  let s5 := execInstrBr s4 (.BEQ .x19 .x10 16)
  let s6 := execInstrBr s5 (.JAL .x0 16)
  let s7 := execInstrBr s6 (.ADD .x20 .x7 .x0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := normal_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 3)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x0 65)) 6
  · have hp : s1.pc = 0x1280 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x19 .x10 16)) 5
  · have hp : s2.pc = 0x1284 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 66)) 4
  · have hp : s3.pc = 0x1288 := by
      simp [s1,s2,s3,execInstrBr,pc,not65,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.BEQ .x19 .x10 16)) 3
  · have hp : s4.pc = 0x128c := by
      simp [s1,s2,s3,s4,execInstrBr,pc,not65,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.JAL .x0 16)) 2
  · have hp : s5.pc = 0x1290 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,not65,not66,
        signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x20 .x7 .x0)) 1
  · have hp : s6.pc = 0x12a0 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,not65,not66,
        signExtend12,signExtend21,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (normal s) _ (.base (.ADDI .x21 .x0 0)) 0
  · have hp : s7.pc = 0x12a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,not65,not66,
        signExtend12,signExtend21,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem normal_fields (s : MachineState) (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64) (not66 : s.getReg .x19 ≠ 66#64) :
    (normal s).pc = 0x12a8 ∧
    (normal s).getReg .x20 = 3 ∧
    (normal s).getReg .x21 = 0 ∧
    (normal s).getReg .x19 = s.getReg .x19 := by
  simp [normal,GroupedBalancedKeygenWotsSelector67.selectorState,
    execInstrBr,pc,not65,not66,signExtend12,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def special65 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 3)
  let s := execInstrBr s (.ADDI .x10 .x0 65)
  let s := execInstrBr s (.BEQ .x19 .x10 16)
  let s := execInstrBr s (.ADDI .x7 .x0 8)
  let s := execInstrBr s (.JAL .x0 8)
  let s := execInstrBr s (.ADD .x20 .x7 .x0)
  execInstrBr s (.ADDI .x21 .x0 0)

private theorem code65 :
    Keygen.instructionAt image 0x1294 = some (.base (.ADDI .x7 .x0 8)) ∧
    Keygen.instructionAt image 0x1298 = some (.base (.JAL .x0 8)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem special65_steps (s : MachineState) (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64) :
    OrdinarySteps image s 7 (special65 s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 3)
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 65)
  let s3 := execInstrBr s2 (.BEQ .x19 .x10 16)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 8)
  let s5 := execInstrBr s4 (.JAL .x0 8)
  let s6 := execInstrBr s5 (.ADD .x20 .x7 .x0)
  obtain ⟨c0,c1,c2,_,_,_,c6,c7⟩ := normal_code
  obtain ⟨c3,c4⟩ := code65
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 3)) 6
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x0 65)) 5
  · have hp : s1.pc = 0x1280 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x19 .x10 16)) 4
  · have hp : s2.pc = 0x1284 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 8)) 3
  · have hp : s3.pc = 0x1294 := by
      simp [s1,s2,s3,execInstrBr,pc,index,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.JAL .x0 8)) 2
  · have hp : s4.pc = 0x1298 := by
      simp [s1,s2,s3,s4,execInstrBr,pc,index,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x20 .x7 .x0)) 1
  · have hp : s5.pc = 0x12a0 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,index,signExtend12,signExtend13,signExtend21,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s6 (special65 s) _ (.base (.ADDI .x21 .x0 0)) 0
  · have hp : s6.pc = 0x12a4 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,index,signExtend12,signExtend13,signExtend21,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem special65_fields (s : MachineState) (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64) :
    (special65 s).pc = 0x12a8 ∧
    (special65 s).getReg .x20 = 8 ∧
    (special65 s).getReg .x21 = 0 ∧
    (special65 s).getReg .x19 = s.getReg .x19 := by
  simp [special65,execInstrBr,pc,index,signExtend12,signExtend13,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

def special66 (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 3)
  let s := execInstrBr s (.ADDI .x10 .x0 65)
  let s := execInstrBr s (.BEQ .x19 .x10 16)
  let s := execInstrBr s (.ADDI .x10 .x0 66)
  let s := execInstrBr s (.BEQ .x19 .x10 16)
  let s := execInstrBr s (.ADDI .x7 .x0 10)
  let s := execInstrBr s (.ADD .x20 .x7 .x0)
  execInstrBr s (.ADDI .x21 .x0 0)

private theorem code66 :
    Keygen.instructionAt image 0x129c = some (.base (.ADDI .x7 .x0 10)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem special66_steps (s : MachineState) (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64) :
    OrdinarySteps image s 8 (special66 s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 3)
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 65)
  let s3 := execInstrBr s2 (.BEQ .x19 .x10 16)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 66)
  let s5 := execInstrBr s4 (.BEQ .x19 .x10 16)
  let s6 := execInstrBr s5 (.ADDI .x7 .x0 10)
  let s7 := execInstrBr s6 (.ADD .x20 .x7 .x0)
  obtain ⟨c0,c1,c2,c3,c4,_,c6,c7⟩ := normal_code
  have c5 := code66
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 3)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x0 65)) 6
  · have hp : s1.pc = 0x1280 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x19 .x10 16)) 5
  · have hp : s2.pc = 0x1284 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 66)) 4
  · have hp : s3.pc = 0x1288 := by
      simp [s1,s2,s3,execInstrBr,pc,index,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.BEQ .x19 .x10 16)) 3
  · have hp : s4.pc = 0x128c := by
      simp [s1,s2,s3,s4,execInstrBr,pc,index,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x7 .x0 10)) 2
  · have hp : s5.pc = 0x129c := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc,index,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x20 .x7 .x0)) 1
  · have hp : s6.pc = 0x12a0 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,index,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 (special66 s) _ (.base (.ADDI .x21 .x0 0)) 0
  · have hp : s7.pc = 0x12a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,index,signExtend12,signExtend13,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem special66_fields (s : MachineState) (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64) :
    (special66 s).pc = 0x12a8 ∧
    (special66 s).getReg .x20 = 10 ∧
    (special66 s).getReg .x21 = 0 ∧
    (special66 s).getReg .x19 = s.getReg .x19 := by
  simp [special66,execInstrBr,pc,index,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms normal_steps
#print axioms normal_fields
#print axioms special65_steps
#print axioms special65_fields
#print axioms special66_steps
#print axioms special66_fields

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsSelectorAll67

end

/-! Uniform execution and resource count for one direct67 keygen WOTS chain. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsHashPrelude67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsFirstHash67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsLoopAdvance67
open SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsRunTicks67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def firstEnd (hash : Hash) (s : MachineState) : MachineState :=
  advanceState (writeHash (preludeState s) (hash (hashInput (preludeState s))))

theorem post_selector (hash : Hash) (s : MachineState) (maxStep : Nat)
    (pc : s.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : s.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : s.getReg .x21 = 0) :
    ∃ final,
      Trace hash image s (4*maxStep+6) (11*maxStep+6)
        maxStep maxStep final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x21 = BitVec.ofNat 64 maxStep ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  let next := advanceState hashed
  obtain ⟨readyPC,service,source,bits,destination,chain,readyMax,readyZero⟩ :=
    prelude_fields s pc
  have first : Trace hash image s 8 15 1 1 hashed := by
    simpa only [image,GroupedBalancedKeygenWotsFirstHash67.image,hashed,prepared]
      using hash_call hash s pc
  have hashedPC : hashed.pc = 0x12c8 := by
    simp [hashed,prepared,writeHash,readyPC]
  have second : Trace hash image hashed 2 2 0 0 next := by
    simpa only [image,GroupedBalancedKeygenWotsLoopAdvance67.image,next]
      using (advance_steps hashed hashedPC).trace (hash := hash)
  have hashedReg (r : Reg) : hashed.getReg r = prepared.getReg r := by
    simp [hashed,writeHash,MachineState.getReg_setPC]
  have nextFields := advance_fields hashed hashedPC
  have countEq : 1 + (maxStep-1) = maxStep := by omega
  have nextPC : next.pc = 0x12c0 := by
    have ne : (1 : Word) ≠ BitVec.ofNat 64 maxStep := by
      intro eq
      have heq := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : maxStep < 2^64)] at heq
      omega
    calc
      next.pc =
          (if hashed.getReg .x21 + 1 ≠ hashed.getReg .x20 then 0x12c0 else 0x12d0) :=
        nextFields.1
      _ = (if (0 : Word) + 1 ≠ BitVec.ofNat 64 maxStep then 0x12c0 else 0x12d0) := by
        rw [hashedReg .x21,hashedReg .x20,readyZero,readyMax,zero,maxReg]
      _ = 0x12c0 := by
        have cond : (0 : Word) + 1 ≠ BitVec.ofNat 64 maxStep := by
          have add01 : (0 : Word) + 1 = 1 := by decide
          rw [add01]
          exact ne
        exact if_pos cond
  have nextStep : next.getReg .x21 = BitVec.ofNat 64 1 := by
    rw [nextFields.2.1,hashedReg .x21,readyZero,zero]
    decide
  have nextMax : next.getReg .x20 = BitVec.ofNat 64 maxStep := by
    rw [nextFields.2.2.1,hashedReg .x20,readyMax,maxReg]
  have nextReg (r : Reg) (different : r ≠ .x21) :
      next.getReg r = prepared.getReg r := by
    rw [advance_reg_stable hashed r different,hashedReg]
  have nextService : next.getReg .x5 = 1 :=
    (nextReg .x5 (by decide)).trans service
  have nextSource : next.getReg .x10 = 0x80000 :=
    (nextReg .x10 (by decide)).trans source
  have nextBits : next.getReg .x11 = 384 :=
    (nextReg .x11 (by decide)).trans bits
  have nextDestination : next.getReg .x12 = 0x80020 :=
    (nextReg .x12 (by decide)).trans destination
  obtain ⟨final,rest,done,finalStep,finalReg,finalCounter,finalLevel,finalLeaf⟩ :=
    run_ticks hash next 1 (maxStep-1) (by omega) (by omega)
      nextPC nextStep (by simpa only [countEq] using nextMax)
      nextService nextSource nextBits nextDestination
  have preparedCounter : prepared.getMem 0x81030 = s.getMem 0x81030 := by
    rw [GroupedBalancedKeygenWotsHashPrelude67.prelude_mem s 0x81030,
      if_neg (by decide)]
  have hashedCounter : hashed.getMem 0x81030 = prepared.getMem 0x81030 := by
    exact GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
      (hash (hashInput prepared)) destination 0x81030
      (by intro i; fin_cases i <;> decide)
  have nextCounter : next.getMem 0x81030 = s.getMem 0x81030 := by
    rw [advance_mem,hashedCounter,preparedCounter]
  have preparedLevel : prepared.getMem 0x81000 = s.getMem 0x81000 := by
    rw [GroupedBalancedKeygenWotsHashPrelude67.prelude_mem s 0x81000,
      if_neg (by decide)]
  have hashedLevel : hashed.getMem 0x81000 = prepared.getMem 0x81000 := by
    exact GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
      (hash (hashInput prepared)) destination 0x81000
      (by intro i; fin_cases i <;> decide)
  have nextLevel : next.getMem 0x81000 = s.getMem 0x81000 := by
    rw [advance_mem,hashedLevel,preparedLevel]
  have preparedLeaf : prepared.getMem 0x81008 = s.getMem 0x81008 := by
    rw [GroupedBalancedKeygenWotsHashPrelude67.prelude_mem s 0x81008,
      if_neg (by decide)]
  have hashedLeaf : hashed.getMem 0x81008 = prepared.getMem 0x81008 := by
    exact GroupedBalancedKeygenWotsFirstAnswer67.h2_answer_frame prepared
      (hash (hashInput prepared)) destination 0x81008
      (by intro i; fin_cases i <;> decide)
  have nextLeaf : next.getMem 0x81008 = s.getMem 0x81008 := by
    rw [advance_mem,hashedLeaf,preparedLeaf]
  refine ⟨final,?_,done,?_,?_,?_,?_,?_⟩
  · have full := (first.trans second).trans rest
    convert full using 1 <;> omega
  · rw [finalReg .x19 (by decide),nextReg .x19 (by decide),chain]
  · simpa only [countEq] using finalStep
  · rw [finalCounter,nextCounter]
  · rw [finalLevel,nextLevel]
  · rw [finalLeaf,nextLeaf]

#print axioms post_selector

private theorem after_selector (hash : Hash) (s t : MachineState)
    (ordinary : Nat) (maxStep : Nat)
    (path : OrdinarySteps image s ordinary t)
    (pc : t.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (maxReg : t.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : t.getReg .x21 = 0)
    (chain : t.getReg .x19 = s.getReg .x19) :
    ∃ final,
      Trace hash image s (ordinary + (4*maxStep+6))
        (ordinary + (11*maxStep+6)) maxStep maxStep final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x21 = BitVec.ofNat 64 maxStep ∧
      final.getMem 0x81030 = t.getMem 0x81030 ∧
      final.getMem 0x81000 = t.getMem 0x81000 ∧
      final.getMem 0x81008 = t.getMem 0x81008 := by
  obtain ⟨final,rest,done,x19,x21,counter,level,leaf⟩ :=
    post_selector hash t maxStep pc lower upper maxReg zero
  exact ⟨final,by simpa only [Nat.zero_add] using
    (path.trace (hash := hash)).trans rest,done,x19.trans chain,x21,counter,level,leaf⟩

theorem normal_chain (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64) :
    ∃ final,
      Trace hash image s 26 47 3 3 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x21 = 3 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let t := GroupedBalancedKeygenWotsSelector67.selectorState s
  obtain ⟨tpc,tmax,tzero,tx19⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.normal_fields s pc not65 not66
  obtain ⟨final,path,done,x19,x21,counter,level,leaf⟩ :=
    after_selector hash s t 8 3
      (GroupedBalancedKeygenWotsSelectorAll67.normal_steps s pc not65 not66)
      tpc (by decide) (by decide) tmax tzero tx19
  have tCounter : t.getMem 0x81030 = s.getMem 0x81030 := by
    simp [t,GroupedBalancedKeygenWotsSelector67.selectorState,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  have tLevel : t.getMem 0x81000 = s.getMem 0x81000 := by
    simp [t,GroupedBalancedKeygenWotsSelector67.selectorState,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  have tLeaf : t.getMem 0x81008 = s.getMem 0x81008 := by
    simp [t,GroupedBalancedKeygenWotsSelector67.selectorState,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,x19,by simpa using x21,counter.trans tCounter,level.trans tLevel,
    leaf.trans tLeaf⟩

theorem special65_chain (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64) :
    ∃ final,
      Trace hash image s 45 101 8 8 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x21 = 8 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special65 s
  obtain ⟨tpc,tmax,tzero,tx19⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special65_fields s pc index
  obtain ⟨final,path,done,x19,x21,counter,level,leaf⟩ :=
    after_selector hash s t 7 8
      (GroupedBalancedKeygenWotsSelectorAll67.special65_steps s pc index)
      tpc (by decide) (by decide) tmax tzero tx19
  have tCounter : t.getMem 0x81030 = s.getMem 0x81030 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special65,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  have tLevel : t.getMem 0x81000 = s.getMem 0x81000 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special65,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  have tLeaf : t.getMem 0x81008 = s.getMem 0x81008 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special65,execInstrBr,
      signExtend12,signExtend13,signExtend21]
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,x19,by simpa using x21,counter.trans tCounter,level.trans tLevel,
    leaf.trans tLeaf⟩

theorem special66_chain (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64) :
    ∃ final,
      Trace hash image s 54 124 10 10 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x21 = 10 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special66 s
  obtain ⟨tpc,tmax,tzero,tx19⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special66_fields s pc index
  obtain ⟨final,path,done,x19,x21,counter,level,leaf⟩ :=
    after_selector hash s t 8 10
      (GroupedBalancedKeygenWotsSelectorAll67.special66_steps s pc index)
      tpc (by decide) (by decide) tmax tzero tx19
  have tCounter : t.getMem 0x81030 = s.getMem 0x81030 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special66,execInstrBr,
      signExtend12,signExtend13]
  have tLevel : t.getMem 0x81000 = s.getMem 0x81000 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special66,execInstrBr,
      signExtend12,signExtend13]
  have tLeaf : t.getMem 0x81008 = s.getMem 0x81008 := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special66,execInstrBr,
      signExtend12,signExtend13]
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,x19,by simpa using x21,counter.trans tCounter,level.trans tLevel,
    leaf.trans tLeaf⟩

#print axioms normal_chain
#print axioms special65_chain
#print axioms special66_chain

theorem regular_from_entry (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64) :
    ∃ final,
      Trace hash image s 67 88 3 3 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyNot65 : ready.getReg .x19 ≠ 65#64 := by rw [readyX19]; exact not65
  have readyNot66 : ready.getReg .x19 ≠ 66#64 := by rw [readyX19]; exact not66
  obtain ⟨final,tail,done,x19,_,counter,level,leaf⟩ :=
    normal_chain hash ready readyPC readyNot65 readyNot66
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLevel : ready.getMem 0x81000 = s.getMem 0x81000 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLeaf : ready.getMem 0x81008 = s.getMem 0x81008 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans tail,
    done,x19.trans readyX19,counter.trans readyCounter,level.trans readyLevel,
    leaf.trans readyLeaf⟩

theorem special65_from_entry (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 65#64) :
    ∃ final,
      Trace hash image s 86 142 8 8 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 65#64 := readyX19.trans index
  obtain ⟨final,tail,done,x19,_,counter,level,leaf⟩ :=
    special65_chain hash ready readyPC readyIndex
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLevel : ready.getMem 0x81000 = s.getMem 0x81000 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLeaf : ready.getMem 0x81008 = s.getMem 0x81008 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans tail,
    done,x19.trans readyX19,counter.trans readyCounter,level.trans readyLevel,
    leaf.trans readyLeaf⟩

theorem special66_from_entry (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x11d8)
    (index : s.getReg .x19 = 66#64) :
    ∃ final,
      Trace hash image s 95 165 10 10 final ∧
      final.pc = 0x12d0 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      final.getMem 0x81000 = s.getMem 0x81000 ∧
      final.getMem 0x81008 = s.getMem 0x81008 := by
  let ready := GroupedBalancedKeygenWotsPrepared67.wotsState s
  have readyPC := GroupedBalancedKeygenWotsPrepared67.wots_pc s pc
  have readyX19 := GroupedBalancedKeygenWotsFirstInput67.x19_wots s pc
  have readyIndex : ready.getReg .x19 = 66#64 := readyX19.trans index
  obtain ⟨final,tail,done,x19,_,counter,level,leaf⟩ :=
    special66_chain hash ready readyPC readyIndex
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLevel : ready.getMem 0x81000 = s.getMem 0x81000 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have readyLeaf : ready.getMem 0x81008 = s.getMem 0x81008 := by
    simp [ready,GroupedBalancedKeygenWotsPrepared67.wotsState,
      GroupedBalancedKeygenWotsPrepared67.all_mem,
      GroupedBalancedKeygenWotsHeader67.header_mem_other,
      GroupedBalancedKeygenWotsHeader67.reset_mem_other]
  have first : Trace hash image s 41 41 0 0 ready :=
    (GroupedBalancedKeygenWotsPrepared67.wots_steps s pc).trace (hash := hash)
  exact ⟨final,by simpa only [Nat.reduceAdd] using first.trans tail,
    done,x19.trans readyX19,counter.trans readyCounter,level.trans readyLevel,
    leaf.trans readyLeaf⟩

#print axioms regular_from_entry
#print axioms special65_from_entry
#print axioms special66_from_entry

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenWotsChainRun67
