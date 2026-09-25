import SigGolfCandidate.Hypertree.VerifyHoistHash

namespace SigGolfCandidate.Hypertree.Verifying.Hoist
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen Signing
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

def LoopCode (image : Image) : Prop :=
  TickCode image ∧
  instructionAt image 0x1930 = some (.base (.BEQ .x30 .x31 (-756))) ∧
  instructionAt image 0x1944 = some (.base (.JAL .x0 (-776)))

def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BEQ .x30 .x31 (-756))

def exitState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 (-776))

theorem branch_block (image : Image) (code : LoopCode image)
    (s : MachineState) (pc : s.pc = 0x1930) :
    OrdinarySteps image s 1 (branchState s) := by
  apply OrdinarySteps.step s _ _ (.base (.BEQ .x30 .x31 (-756))) 0
  · simpa only [fetch_at,pc] using code.2.1
  · rfl
  exact OrdinarySteps.refl _

theorem exit_block (image : Image) (code : LoopCode image)
    (s : MachineState) (pc : s.pc = 0x1944) :
    OrdinarySteps image s 1 (exitState s) := by
  apply OrdinarySteps.step s _ _ (.base (.JAL .x0 (-776))) 0
  · simpa only [fetch_at,pc] using code.2.2
  · rfl
  exact OrdinarySteps.refl _

theorem branch_pc (s : MachineState) (step : Nat)
    (pc : s.pc = 0x1930) (reg : s.getReg .x30 = BitVec.ofNat 64 step)
    (seven : s.getReg .x31 = 7) (bound : step ≤ 7) :
    (branchState s).pc = if step = 7 then 0x163c else 0x1934 := by
  simp [branchState,execInstrBr,signExtend13,pc,reg,seven]
  interval_cases step <;> decide

theorem exit_pc (s : MachineState) (pc : s.pc = 0x1944) :
    (exitState s).pc = 0x163c := by
  norm_num [exitState,execInstrBr,pc,signExtend21]
  decide

theorem branch_mem (s : MachineState) (a : Word) :
    (branchState s).getMem a = s.getMem a := by simp [branchState,execInstrBr]

theorem exit_mem (s : MachineState) (a : Word) :
    (exitState s).getMem a = s.getMem a := by simp [exitState,execInstrBr]

theorem branch_regs (s : MachineState) (r : Reg) :
    (branchState s).getReg r = s.getReg r := by simp [branchState,execInstrBr]

theorem exit_regs (s : MachineState) (r : Reg) :
    (exitState s).getReg r = s.getReg r := by
  by_cases h : r = .x0
  · subst r
    simp only [exitState,execInstrBr,MachineState.getReg_setPC,
      MachineState.setReg,MachineState.getReg]
  · simp only [exitState,execInstrBr,MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne s .x0 r (s.pc+4) (Ne.symm h)

theorem LoopData.of_mem_regs {s t : MachineState} {level tree step : Nat}
    {side : Bool} {chain : Reference.Chain} {value : Reference.Digest}
    (data : LoopData s level tree side chain step value)
    (mem : ∀ a, t.getMem a = s.getMem a)
    (regs : ∀ r, t.getReg r = s.getReg r) :
    LoopData t level tree side chain step value := by
  constructor
  · rw [mem]; exact data.headerEq
  · intro i; rw [mem]; exact data.indexEq i
  · intro i; rw [mem]; exact data.valueEq i
  · rw [regs]; exact data.srcEq
  · rw [regs]; exact data.lenEq
  · rw [regs]; exact data.dstEq
  · rw [regs]; exact data.serviceEq
  · rw [regs]; exact data.stepReg
  · rw [regs]; exact data.sevenReg

theorem LoopData.to_word_carry {s : MachineState} {level tree step : Nat}
    {side : Bool} {chain : Reference.Chain} {value : Reference.Digest}
    (data : LoopData s level tree side chain step value) (bound : step < 8) :
    HeaderWordCarry s level tree (Reference.sideNumber side) := by
  refine ⟨chain.val,step,chain.isLt,bound,data.headerEq,data.indexEq,
    data.serviceEq,data.dstEq,data.sevenReg⟩

theorem hash_loop (image : Image) (hash : Hash) (code : LoopCode image)
    (s : MachineState) (level tree step remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1934) (length : step + remaining = 7)
    (positive : 0 < remaining) (levelBound : level < 256)
    (data : LoopData s level tree side chain step value) :
    ∃ final, Trace hash image s (4*remaining+1) (11*remaining+1)
        remaining remaining final ∧ final.pc = 0x163c ∧
      LoopData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) step remaining value) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideTick a → final.getMem a = s.getMem a) := by
  induction remaining generalizing s step value with
  | zero => omega
  | succ remaining ih =>
    have small : step < 7 := by omega
    let next := tickState hash s
    have tick := tick_block image hash code.1 s pc data.serviceEq data.srcEq data.lenEq data.dstEq
    have nextData := tick_data hash s level tree step side chain value small levelBound data
    have nextRA := tick_regs hash s .x1 (by decide)
    have nextSP := tick_regs hash s .x2 (by decide)
    by_cases zero : remaining = 0
    · subst remaining
      have stepSix : step = 6 := by omega
      have nextPC : next.pc = 0x1944 := by
        rw [tick_pc hash s step pc data.stepReg data.sevenReg small]
        simp [stepSix]
      let final := exitState next
      have tail := exit_block image code next nextPC
      refine ⟨final,?_,exit_pc next nextPC,?_,?_,?_,?_⟩
      · convert tick.trans tail.trace using 1 <;> omega
      · have moved := nextData.of_mem_regs (exit_mem next) (exit_regs next)
        simpa [final,stepSix,walk] using moved
      · exact (exit_regs next .x1).trans nextRA
      · exact (exit_regs next .x2).trans nextSP
      · intro a outside
        rw [exit_mem]
        exact tick_frame hash s a data.srcEq data.dstEq outside
    · have nextPC : next.pc = 0x1934 := by
        rw [tick_pc hash s step pc data.stepReg data.sevenReg small]
        have h : step+1 ≠ 7 := by omega
        simp [h]
      obtain ⟨final,tail,finalPC,finalData,finalRA,finalSP,finalFrame⟩ :=
        ih next (step+1) (Reference.chainHash hash level tree side chain step value)
          nextPC (by omega) (by omega) nextData
      refine ⟨final,?_,finalPC,?_,finalRA.trans nextRA,finalSP.trans nextSP,?_⟩
      · convert tick.trans tail using 1 <;> omega
      · simpa only [walk] using finalData
      · intro a outside
        rw [finalFrame a outside]
        exact tick_frame hash s a data.srcEq data.dstEq outside

theorem run_fragment (image : Image) (hash : Hash) (code : LoopCode image)
    (s : MachineState) (level tree step remaining : Nat)
    (side : Bool) (chain : Reference.Chain) (value : Reference.Digest)
    (pc : s.pc = 0x1930) (length : step + remaining = 7)
    (levelBound : level < 256)
    (data : LoopData s level tree side chain step value) :
    ∃ final instructions cycles,
      Trace hash image s instructions cycles remaining remaining final ∧
      instructions ≤ 4*remaining+2 ∧ cycles ≤ 11*remaining+2 ∧
      instructions ≤ cycles ∧
      final.pc = 0x163c ∧
      LoopData final level tree side chain 7
        (walk (Reference.chainHash hash level tree side chain) step remaining value) ∧
      HeaderWordCarry final level tree (Reference.sideNumber side) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideTick a → final.getMem a = s.getMem a) := by
  have pre := branch_block image code s pc
  let ready := branchState s
  have readyData : LoopData ready level tree side chain step value :=
    data.of_mem_regs (branch_mem s) (branch_regs s)
  by_cases zero : remaining = 0
  · have stepSeven : step = 7 := by omega
    have readyPC : ready.pc = 0x163c := by
      rw [branch_pc s step pc data.stepReg data.sevenReg (by omega)]
      simp [stepSeven]
    refine ⟨ready,1,1,?_,by omega,by omega,by omega,readyPC,?_,?_,?_,?_,?_⟩
    · simpa [zero] using pre.trace
    · simpa [zero,stepSeven,walk] using readyData
    · exact readyData.to_word_carry (by omega)
    · exact branch_regs s .x1
    · exact branch_regs s .x2
    · intro a _; exact branch_mem s a
  · have readyPC : ready.pc = 0x1934 := by
      rw [branch_pc s step pc data.stepReg data.sevenReg (by omega)]
      have h : step ≠ 7 := by omega
      simp [h]
    obtain ⟨final,tail,finalPC,finalData,finalRA,finalSP,finalFrame⟩ :=
      hash_loop image hash code ready level tree step remaining side chain value
        readyPC length (by omega) levelBound readyData
    refine ⟨final,4*remaining+2,11*remaining+2,?_,by omega,by omega,by omega,
      finalPC,finalData,finalData.to_word_carry (by decide),?_,?_,?_⟩
    · convert pre.trace.trans tail using 1 <;> omega
    · exact finalRA.trans (branch_regs s .x1)
    · exact finalSP.trans (branch_regs s .x2)
    · intro a outside
      rw [finalFrame a outside]
      exact branch_mem s a

end SigGolfCandidate.Hypertree.Verifying.Hoist
