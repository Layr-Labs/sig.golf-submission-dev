import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroup67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyFooter67

/-! The forty-fifth group falls through to the root comparison. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupFinish67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyEndGroup67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def finishState (s : MachineState) : MachineState :=
  let s := countState s
  let s := execInstrBr s (.BEQ .x6 .x7 8)
  let s := execInstrBr s (.JAL .x0 20)
  let s := execInstrBr s (.ADDI .x7 .x0 45)
  execInstrBr s (.BNE .x6 .x7 (-1260))

private theorem finish_code :
    Keygen.instructionAt image 0x19e4 =
      some (.base (.BEQ .x6 .x7 8)) ∧
    Keygen.instructionAt image 0x19e8 =
      some (.base (.JAL .x0 20)) ∧
    Keygen.instructionAt image 0x19fc =
      some (.base (.ADDI .x7 .x0 45)) ∧
    Keygen.instructionAt image 0x1a00 =
      some (.base (.BNE .x6 .x7 (-1260))) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem finish_steps (s : MachineState)
    (pc : s.pc = 0x19c4)
    (h30 : (countState s).getReg .x6 ≠
      (countState s).getReg .x7) :
    OrdinarySteps image (countState s) 4 (finishState s) := by
  let s1 := execInstrBr (countState s) (.BEQ .x6 .x7 8)
  let s2 := execInstrBr s1 (.JAL .x0 20)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 45)
  obtain ⟨c0,c1,c2,c3⟩ := finish_code
  have pc0 : (countState s).pc = 0x19e4 := count_pc s pc
  have pc1 : s1.pc = 0x19e8 := by
    simp [s1,execInstrBr,pc0,h30]
  have pc2 : s2.pc = 0x19fc := by
    simp [s2,execInstrBr,pc1,signExtend21]
  have pc3 : s3.pc = 0x1a00 := by
    simp [s3,execInstrBr,pc2]
  apply OrdinarySteps.step (countState s) s1 _
      (.base (.BEQ .x6 .x7 8)) 3
  · simpa only [Keygen.fetch_at,pc0] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.JAL .x0 20)) 2
  · simpa only [Keygen.fetch_at,pc1] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 45)) 1
  · simpa only [Keygen.fetch_at,pc2] using c2
  · rfl
  apply OrdinarySteps.step s3 (finishState s) _
      (.base (.BNE .x6 .x7 (-1260))) 0
  · simpa only [Keygen.fetch_at,pc3] using c3
  · rfl
  exact OrdinarySteps.refl _

theorem finish_pc (s : MachineState)
    (pc : s.pc = 0x19c4) (group : s.getMem 0x81058 = 44) :
    (finishState s).pc = 0x1a04 := by
  let s1 := execInstrBr (countState s) (.BEQ .x6 .x7 8)
  let s2 := execInstrBr s1 (.JAL .x0 20)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 45)
  have x6 : (countState s).getReg .x6 = 45 := by
    rw [count_x6,group]
    decide
  have x7 : (countState s).getReg .x7 = 30 := count_x7 s
  have pc0 := count_pc s pc
  have pc1 : s1.pc = 0x19e8 := by
    simp [s1,execInstrBr,pc0,x6,x7]
  have pc2 : s2.pc = 0x19fc := by
    simp [s2,execInstrBr,pc1,signExtend21]
  have pc3 : s3.pc = 0x1a00 := by
    simp [s3,execInstrBr,pc2]
  have hx6 : s3.getReg .x6 = 45 := by
    simp [s3,s2,s1,execInstrBr,x6,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hx7 : s3.getReg .x7 = 45 := by
    simp [s3,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  change (execInstrBr s3 (.BNE .x6 .x7 (-1260))).pc = 0x1a04
  simp [execInstrBr,pc3,hx6,hx7]

theorem finish_mem (s : MachineState) (a : Word)
    (ne : a ≠ 0x81058) :
    (finishState s).getMem a = s.getMem a := by
  simpa [finishState,execInstrBr] using count_mem s a ne

theorem finish_root_matches (s : MachineState) :
    Signing.RootMatches (finishState s) ↔ Signing.RootMatches s := by
  unfold Signing.RootMatches
  rw [finish_mem s 0x80500 (by decide),
    finish_mem s 0x80508 (by decide),
    finish_mem s 0x40 (by decide),
    finish_mem s 0x48 (by decide)]

theorem final_group_executes (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x19c4) (group : s.getMem 0x81058 = 44) :
    ∃ (steps : Nat) (final : MachineState), steps ≤ 27 ∧
      Executes hash image s steps
        ⟨if Signing.RootMatches s then .success else .failure,
          final, steps, 0, 0⟩ ∧
      ∀ a, a ≠ 0x81058 → final.getMem a = s.getMem a := by
  obtain ⟨more,final,bound,suffix,frame⟩ :=
    GroupedBalancedVerifyFooter67.footer_executes hash (finishState s)
      (finish_pc s pc group)
  have h30 : (countState s).getReg .x6 ≠
      (countState s).getReg .x7 := by
    rw [count_x6,count_x7,group]
    decide
  have pre : OrdinarySteps image s 12 (finishState s) :=
    Keygen.ordinary_trans image s (countState s) (finishState s)
      8 4 (count_steps s pc) (finish_steps s pc h30)
  have combined := (OrdinarySteps.trace (hash := hash) pre).then_executes
    suffix
  refine ⟨12+more,final,by omega,?_,?_⟩
  · simpa [Execution.charge,finish_root_matches] using combined
  · intro a ne
    rw [frame a,finish_mem s a ne]

#print axioms finish_steps
#print axioms finish_pc
#print axioms finish_mem
#print axioms final_group_executes
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupFinish67
