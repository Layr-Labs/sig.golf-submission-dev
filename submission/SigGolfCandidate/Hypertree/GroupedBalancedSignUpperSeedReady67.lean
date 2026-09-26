import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedDispatch67
import SigGolfCandidate.Hypertree.SignCopy
import SigGolfCandidate.Hypertree.KeygenCopyX19
import SigGolfCandidate.Hypertree.KeygenCopyX2X19
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOdd67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEven67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedReady67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEven67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x81)
  let s := execInstrBr s (.ADDI .x6 .x6 0xd00)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x20)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x18bc = some (.base (.LUI .x6 0x81)) ∧
    Keygen.instructionAt image 0x18c0 = some (.base (.ADDI .x6 .x6 0xd00)) ∧
    Keygen.instructionAt image 0x18c4 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x18c8 = some (.base (.ADDI .x7 .x7 0x20)) ∧
    Keygen.instructionAt image 0x18cc = some (.base (.ADDI .x10 .x0 2)) := by decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x18bc) :
    OrdinarySteps image s 5 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x81)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0xd00)
  let s3 := execInstrBr s2 (.LUI .x7 0x80)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 0x20)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0xd00)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 0x20)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (setupState s) _ (.base (.ADDI .x10 .x0 2)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x18bc) :
    (setupState s).pc = 0x18d0 := by
  simp [setupState,execInstrBr,pc]

theorem setup_frame (s : MachineState) (a : Word) :
    (setupState s).getMem a = s.getMem a := by
  simp [setupState,execInstrBr]

theorem copy_code : Keygen.CopyCode image 0x18d0 := by decide

theorem copy_inv (s : MachineState) (pc : s.pc = 0x18bc) :
    Keygen.CopyInvariant 0x18d0 0x80d00 0x80020 2 2 (setupState s) := by
  unfold Keygen.CopyInvariant setupState
  simp [execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12,pc]

theorem seed_copy (s : MachineState) (pc : s.pc = 0x18bc) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x18e8 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d00 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let begun := setupState s
  obtain ⟨final,loopTrace,done,words,frame,x19,sp⟩ :=
    KeygenCopyX2X19.copy_all_x19_x2 image
    0x18d0 copy_code 0x80d00 0x80020 2 begun
    (copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,done.2.2.1,?_,?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s begun final 5 12
      (setup_steps s pc) loopTrace
    simpa only [Nat.reduceAdd] using full
  · rw [x19]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]
  · rw [sp]
    simp [begun,setupState,execInstrBr,MachineState.getReg_setReg_ne]
  · intro i hi
    rw [words i hi,setup_frame]
  · intro a outside
    rw [frame a outside,setup_frame]

#print axioms seed_copy
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEven67

end

/-! The two parity branches both leave a 16-byte chain seed at 0x80020. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedReady67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def jumpState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 0x30)

private theorem jump_code :
    Keygen.instructionAt image 0x18b8 = some (.base (.JAL .x0 0x30)) := by decide

theorem jump_steps (s : MachineState) (pc : s.pc = 0x18b8) :
    OrdinarySteps image s 1 (jumpState s) := by
  apply OrdinarySteps.step s (jumpState s) _ (.base (.JAL .x0 0x30)) 0
  · simpa only [Keygen.fetch_at,pc] using jump_code
  · rfl
  exact OrdinarySteps.refl _

theorem jump_pc (s : MachineState) (pc : s.pc = 0x18b8) :
    (jumpState s).pc = 0x18e8 := by
  simp [jumpState,execInstrBr,signExtend21,pc]

theorem jump_frame (s : MachineState) (a : Word) :
    (jumpState s).getMem a = s.getMem a := by
  simp [jumpState,execInstrBr]

theorem jump_x19 (s : MachineState) :
    (jumpState s).getReg .x19 = s.getReg .x19 := by
  simp [jumpState,execInstrBr,MachineState.getReg_setReg_ne]

theorem jump_x2 (s : MachineState) :
    (jumpState s).getReg .x2 = s.getReg .x2 := by
  simp [jumpState,execInstrBr,MachineState.getReg_setReg_ne]

theorem dispatch_x19 (s : MachineState) :
    (GroupedBalancedSignUpperSeedDispatch67.dispatchState s).getReg .x19 =
      s.getReg .x19 := by
  simp [GroupedBalancedSignUpperSeedDispatch67.dispatchState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem dispatch_x2 (s : MachineState) :
    (GroupedBalancedSignUpperSeedDispatch67.dispatchState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperSeedDispatch67.dispatchState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem even_ready (s : MachineState) (pc : s.pc = 0x1884)
    (even : s.getReg .x19 &&& (1 : Word) = 0) :
    ∃ final, OrdinarySteps image s 19 final ∧ final.pc = 0x18e8 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d00 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let d := GroupedBalancedSignUpperSeedDispatch67.dispatchState s
  have dpc : d.pc = 0x18bc := by
    rw [GroupedBalancedSignUpperSeedDispatch67.dispatch_pc s pc,if_pos even]
  obtain ⟨final,copy,done,x19,sp,words,frame⟩ :=
    GroupedBalancedSignUpperSeedEven67.seed_copy d dpc
  refine ⟨final,?_,done,?_,?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s d final 2 17
      (GroupedBalancedSignUpperSeedDispatch67.dispatch_steps s pc) copy
    simpa only [Nat.reduceAdd] using full
  · exact x19.trans (dispatch_x19 s)
  · exact sp.trans (dispatch_x2 s)
  · intro i hi
    rw [words i hi,GroupedBalancedSignUpperSeedDispatch67.dispatch_frame]
  · intro a outside
    rw [frame a outside,GroupedBalancedSignUpperSeedDispatch67.dispatch_frame]

theorem odd_ready (s : MachineState) (pc : s.pc = 0x1884)
    (odd : s.getReg .x19 &&& (1 : Word) ≠ 0) :
    ∃ final, OrdinarySteps image s 20 final ∧ final.pc = 0x18e8 ∧
      final.getReg .x19 = s.getReg .x19 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x80020 i) =
        s.getMem (Signing.wordAddress 0x80d10 i)) ∧
      (∀ a, (∀ i, i < 2 → a ≠ Signing.wordAddress 0x80020 i) →
        final.getMem a = s.getMem a) := by
  let d := GroupedBalancedSignUpperSeedDispatch67.dispatchState s
  have dpc : d.pc = 0x188c := by
    rw [GroupedBalancedSignUpperSeedDispatch67.dispatch_pc s pc,if_neg odd]
  obtain ⟨copied,copy,copyPc,x19,sp,words,frame⟩ :=
    GroupedBalancedSignUpperSeedOdd67.seed_copy d dpc
  let final := jumpState copied
  refine ⟨final,?_,jump_pc copied copyPc,?_,?_,?_,?_⟩
  · have first := Keygen.ordinary_trans image s d copied 2 17
      (GroupedBalancedSignUpperSeedDispatch67.dispatch_steps s pc) copy
    have full := Keygen.ordinary_trans image s copied final 19 1
      (by simpa only [Nat.reduceAdd] using first)
      (jump_steps copied copyPc)
    simpa only [Nat.reduceAdd] using full
  · rw [jump_x19,x19,dispatch_x19]
  · rw [jump_x2,sp,dispatch_x2]
  · intro i hi
    rw [jump_frame,words i hi,
      GroupedBalancedSignUpperSeedDispatch67.dispatch_frame]
  · intro a outside
    rw [jump_frame,frame a outside,
      GroupedBalancedSignUpperSeedDispatch67.dispatch_frame]

#print axioms even_ready
#print axioms odd_ready
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedReady67
