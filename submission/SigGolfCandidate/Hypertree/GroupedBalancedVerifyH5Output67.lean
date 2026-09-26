import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Loaded67
import SigGolfCandidate.Hypertree.GroupedBalancedSignRandomizer67

/-! Copy the first two H5 answer words into the verifier's index scratch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Output67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

def copySetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x300)
  let s := execInstrBr s (.LUI .x7 0x81)
  let s := execInstrBr s (.ADDI .x7 .x7 8)
  execInstrBr s (.ADDI .x10 .x0 2)

private theorem setup_code :
    Keygen.instructionAt image 0x1114 = some (.base (.LUI .x6 0x80)) ∧
    Keygen.instructionAt image 0x1118 = some (.base (.ADDI .x6 .x6 0x300)) ∧
    Keygen.instructionAt image 0x111c = some (.base (.LUI .x7 0x81)) ∧
    Keygen.instructionAt image 0x1120 = some (.base (.ADDI .x7 .x7 8)) ∧
    Keygen.instructionAt image 0x1124 = some (.base (.ADDI .x10 .x0 2)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1114) :
    OrdinarySteps image s 5 (copySetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x300)
  let s3 := execInstrBr s2 (.LUI .x7 0x81)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  obtain ⟨c0,c1,c2,c3,c4⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x300)) 3
  · have hp : s1.pc = 0x1118 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x7 0x81)) 2
  · have hp : s2.pc = 0x111c := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 1
  · have hp : s3.pc = 0x1120 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (copySetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · have hp : s4.pc = 0x1124 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x1114) :
    (copySetup s).pc = 0x1128 := by simp [copySetup,execInstrBr,pc]

theorem setup_regs (s : MachineState) :
    (copySetup s).getReg .x6 = 0x80300 ∧
    (copySetup s).getReg .x7 = 0x81008 ∧
    (copySetup s).getReg .x10 = 2 := by
  simp [copySetup,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_mem (s : MachineState) (a : Word) :
    (copySetup s).getMem a = s.getMem a := by
  simp [copySetup,execInstrBr]

private theorem copy_code : Keygen.CopyCode image 0x1128 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem output_copy (s : MachineState) (pc : s.pc = 0x1114) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1140 ∧
      (∀ i, i < 2 → final.getMem (Signing.wordAddress 0x81008 i) =
        s.getMem (Signing.wordAddress 0x80300 i)) ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  let setup := copySetup s
  have setupRun := setup_steps s pc
  obtain ⟨src,dst,count⟩ := setup_regs s
  have inv : Keygen.CopyInvariant 0x1128 0x80300 0x81008 2 2 setup := by
    simp [Keygen.CopyInvariant,setup,setup_pc s pc,src,dst,count]
  obtain ⟨final,copyRun,done,words,frame,_,_⟩ :=
    Keygen.copy_all_frame image 0x1128 copy_code 0x80300 0x81008 2 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,?_,?_⟩
  · simpa only [Nat.reduceAdd] using Keygen.ordinary_trans image s setup final
      5 12 setupRun copyRun
  · intro i hi
    exact (words i hi).trans (setup_mem s _)
  · have outside : ∀ i, i < 2 → (0x81048 : Word) ≠
        Signing.wordAddress 0x81008 i := by
      intro i hi
      interval_cases i <;> decide
    exact (frame 0x81048 outside).trans (setup_mem s 0x81048)

theorem loaded_output (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial query final,
      initialState program .verify input = some initial ∧
      Trace hash image initial 122 137 1 2 final ∧ final.pc = 0x1140 ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x81008 i.val) =
        (hash (hashInput query)).extractLsb' (64*i.val) 64) ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨initial,query,loaded,beforeTrace,queryPC,service,src,len,dst,pointer⟩ :=
    GroupedBalancedVerifyH5Loaded67.loaded_query hash input
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 896 src (by simpa using len) dst (by decide)
  have hlen : (hashInput query).1 = 896 := by
    simp [hashInput,len,BitVec.toNat_ofNat]
  have hcomp : compressions (hashInput query).1 = 2 := by
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 16 1 2 afterHash := by
    have hf : fetch image query = some (.base .ECALL) := by
      have code : Keygen.instructionAt image 0x1110 = some (.base .ECALL) := by
        unfold image GroupedBalancedVerifyImage67Fast2Byte.image
          GroupedBalancedVerifyImage67Fast2Byte.code
        decide
      simpa only [Keygen.fetch_at,queryPC] using code
    have raw := Trace.hash query afterHash 0 0 0 0 hf service valid
      (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1114 := by
    simpa [afterHash,answer,Keygen.hash_pc,queryPC] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,words,copyPointer⟩ := output_copy afterHash afterPC
  refine ⟨initial,query,final,loaded,?_,finalPC,?_,?_⟩
  · have composed := beforeTrace.trans (hashRun.trans copyRun.trace)
    simpa only [Nat.reduceAdd] using composed
  · intro i
    have copied := words i.val i.isLt
    have result := Signing.hash_answer_word query answer dst
      (⟨i.val,by have h := i.isLt; omega⟩ : Fin 4)
    exact copied.trans (by simpa [afterHash,answer] using result)
  · have hashPointer : afterHash.getMem 0x81048 = query.getMem 0x81048 := by
      exact Signing.hash_answer_frame query answer dst 0x81048
        (by intro i; fin_cases i <;> decide)
    exact copyPointer.trans (hashPointer.trans pointer)

#print axioms output_copy
#print axioms loaded_output
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Output67
