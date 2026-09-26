import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeJoin67
import SigGolfCandidate.Hypertree.KeygenCopySetup

/-! Copy the ordered four-word tree pair into the H4 input buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Input67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

private theorem setup_code : Keygen.CopySetupCode image 0x13b8 0x520 0x20 4 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopySetupCode
  decide

private theorem copy_code : Keygen.CopyCode image 0x13cc := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem copy_input (s : MachineState) (pc : s.pc = 0x13b8) :
    ∃ final, OrdinarySteps image s 29 final ∧ final.pc = 0x13e4 ∧
      (∀ i : Fin 4, final.getMem (Signing.wordAddress 0x80020 i.val) =
        s.getMem (Signing.wordAddress 0x80520 i.val)) ∧
      final.getMem 0x81048 = s.getMem 0x81048 ∧
      final.getMem 0x81050 = s.getMem 0x81050 ∧
      SafeFrame s final := by
  let setup := Keygen.copySetup s 0x520 0x20 4
  have setupRun := Keygen.copy_setup_block image 0x13b8 0x520 0x20 4 setup_code s pc
  have inv : Keygen.CopyInvariant 0x13cc 0x80520 0x80020 4 4 setup := by
    have regs := Keygen.copy_setup_regs s 0x520 0x20 4
    simp only [Keygen.CopyInvariant,setup,Keygen.copy_setup_pc,pc,regs.1,regs.2.1,
      regs.2.2]
    simp [signExtend12]
  obtain ⟨final,copyRun,done,content,frame,_,sp⟩ :=
    Keygen.copy_all_frame image 0x13cc copy_code 0x80520 0x80020 4 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final,?_,?_,?_,?_,?_,?_,
    sp.trans (Keygen.copy_setup_stack s 0x520 0x20 4).2⟩
  · have run := Keygen.ordinary_trans image s setup final 5 24 setupRun copyRun
    simpa only [Nat.reduceAdd] using run
  · simpa using done.2.2.1
  · intro i
    rw [content i.val i.isLt]
    exact Keygen.copy_setup_mem s 0x520 0x20 4 _
  · rw [frame 0x81048 (by intro i hi; interval_cases i <;> decide)]
    exact Keygen.copy_setup_mem s 0x520 0x20 4 _
  · rw [frame 0x81050 (by intro i hi; interval_cases i <;> decide)]
    exact Keygen.copy_setup_mem s 0x520 0x20 4 _
  · intro a ha
    rw [frame a (by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp [Signing.wordAddress] at hn
      omega)]
    exact Keygen.copy_setup_mem s 0x520 0x20 4 _

theorem loaded_input (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n final,
      initialState program .verify input = some initial ∧
      (n = 306 ∨ n = 307) ∧
      Trace hash image initial n (n+22) 2 3 final ∧
      final.pc = 0x13e4 ∧ final.getMem 0x81048 = 0x2c730 := by
  obtain ⟨initial,n,joined,loaded,ncases,joinedRun,joinedPC,pointer⟩ :=
    GroupedBalancedVerifyTreeJoin67.loaded_join hash input
  obtain ⟨final,copyRun,copyPC,_,copyPointer,_,_⟩ := copy_input joined joinedPC
  refine ⟨initial,n+29,final,loaded,?_,?_,copyPC,copyPointer.trans pointer⟩
  · rcases ncases with h | h <;> simp [h]
  · have run := joinedRun.trans copyRun.trace
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

#print axioms copy_input
#print axioms loaded_input
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Input67
