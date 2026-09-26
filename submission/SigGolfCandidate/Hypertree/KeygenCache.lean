import SigGolfCandidate.Hypertree.KeygenFunctionalInitial
import SigGolfCandidate.Hypertree.KeygenControl
import SigGolfCandidate.Hypertree.KeygenTrace

/-! Inlined from SigGolfCandidate.Hypertree.KeygenFinish; its only importer was SigGolfCandidate.Hypertree.KeygenCache. -/
section
namespace SigGolfCandidate.Hypertree.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096

def outputSetup (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x80)
  let s := execInstrBr s (.ADDI .x6 .x6 0x500)
  let s := execInstrBr s (.ADDI .x7 .x0 0x40)
  execInstrBr s (.ADDI .x10 .x0 2)

theorem output_setup_block (s : MachineState) (pc : s.pc = 0x1014) :
    OrdinarySteps keygen s 4 (outputSetup s) := by
  let s1 := execInstrBr s (.LUI .x6 0x80)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x500)
  let s3 := execInstrBr s2 (.ADDI .x7 .x0 0x40)
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x80)) 3
  · simp only [fetch, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x500)) 2
  · simp only [fetch, s1, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x7 .x0 0x40)) 1
  · simp only [fetch, s1, s2, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  apply OrdinarySteps.step s3 (outputSetup s) _ (.base (.ADDI .x10 .x0 2)) 0
  · simp only [fetch, s1, s2, s3, execInstrBr, MachineState.setPC, pc, keygen]; decide
  · rfl
  exact OrdinarySteps.refl _

theorem output_setup_pc (s : MachineState) (pc : s.pc = 0x1014) :
    (outputSetup s).pc = 0x1024 := by simp [outputSetup, execInstrBr, pc]

theorem output_setup_regs (s : MachineState) :
    (outputSetup s).getReg .x6 = 0x80500 ∧
    (outputSetup s).getReg .x7 = 0x40 ∧
    (outputSetup s).getReg .x10 = 2 := by
  simp [outputSetup, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem output_setup_mem (s : MachineState) (a : Word) :
    (outputSetup s).getMem a = s.getMem a := by simp [outputSetup, execInstrBr]

theorem output_copy_code : CopyCode keygen 0x1024 := by decide

def outputCopied (s : MachineState) : MachineState :=
  Expansion.loopNext (Expansion.loopNext (outputSetup s))

theorem output_copy_block (s : MachineState) (pc : s.pc = 0x1014) :
    OrdinarySteps keygen (outputSetup s) 12 (outputCopied s) := by
  have regs := output_setup_regs s
  have first := copy_block keygen 0x1024 output_copy_code (outputSetup s)
    (output_setup_pc s pc) (by rw [regs.1]; decide) (by rw [regs.2.1]; decide)
  have next_pc : (Expansion.loopNext (outputSetup s)).pc = 0x1024 := by
    rw [copy_next_pc, regs.2.2, output_setup_pc s pc]
    decide
  have next_regs := Expansion.loop_next_regs (outputSetup s)
  have second := copy_block keygen 0x1024 output_copy_code (Expansion.loopNext (outputSetup s))
    next_pc (by rw [next_regs.1, regs.1]; decide) (by rw [next_regs.2.1, regs.2.1]; decide)
  exact ordinary_trans keygen _ _ _ 6 6 first second

theorem output_copied_pc (s : MachineState) (pc : s.pc = 0x1014) :
    (outputCopied s).pc = 0x103c := by
  simp only [outputCopied, copy_next_pc, (Expansion.loop_next_regs (outputSetup s)).2.2,
    (output_setup_regs s).2.2, output_setup_pc s pc]
  decide

theorem output_copied_mem (s : MachineState) (a : Word) :
    (outputCopied s).getMem a =
      if a = 0x48 then s.getMem 0x80508 else
      if a = 0x40 then s.getMem 0x80500 else s.getMem a := by
  simp only [outputCopied, Expansion.loop_next_mem,
    (Expansion.loop_next_regs (outputSetup s)).1,
    (Expansion.loop_next_regs (outputSetup s)).2.1,
    (output_setup_regs s).1, (output_setup_regs s).2.1, output_setup_mem]
  simp

theorem halt_success (hash : Hash) (s : MachineState) (pc : s.pc = 0x103c) :
    Executes hash keygen s 3 ⟨.success, Expansion.finishState s, 3, 0, 0⟩ := by
  have block : OrdinarySteps keygen s 2 (Expansion.finishState s) := by
    apply OrdinarySteps.step s (execInstrBr s (.ADDI .x5 .x0 0)) _ (.base (.ADDI .x5 .x0 0)) 1
    · simp only [fetch, pc, keygen]; decide
    · rfl
    apply OrdinarySteps.step _ (Expansion.finishState s) _ (.base (.ADDI .x10 .x0 1)) 0
    · simp only [fetch, execInstrBr, MachineState.setPC, pc, keygen]; decide
    · rfl
    exact OrdinarySteps.refl _
  have hf : fetch keygen (Expansion.finishState s) = some (.base .ECALL) := by
    simp only [fetch, Expansion.finishState, execInstrBr, MachineState.setPC, pc, keygen]; decide
  have hs : (Expansion.finishState s).getReg .x5 = 0 := by rfl
  have hv : (Expansion.finishState s).getReg .x10 = 1 := by rfl
  simpa [hv, Execution.charge] using block.then_executes (Executes.halt (hash := hash) _ hf hs)

/-- The exact keygen footer always succeeds in 19 cycles and makes no oracle calls. -/
theorem finish (hash : Hash) (s : MachineState) (pc : s.pc = 0x1014) :
    Executes hash keygen s 19 ⟨.success, Expansion.finishState (outputCopied s), 19, 0, 0⟩ := by
  have tail := (output_copy_block s pc).then_executes
    (halt_success hash (outputCopied s) (output_copied_pc s pc))
  simpa [Execution.charge] using (output_setup_block s pc).then_executes tail

/-- The footer writes precisely the two public-key words; all other memory is preserved. -/
theorem finish_mem (s : MachineState) (a : Word) :
    (Expansion.finishState (outputCopied s)).getMem a =
      if a = 0x48 then s.getMem 0x80508 else
      if a = 0x40 then s.getMem 0x80500 else s.getMem a := by
  simpa [Expansion.finishState, execInstrBr] using output_copied_mem s a

/-- Reduction of full keygen execution to its hashed tree-subroutine trace. -/
theorem executes_of_tree_trace (hash : Hash) (s t : MachineState) (pc : s.pc = 0x1000)
    (steps cycles calls blocks : Nat)
    (tree : Trace hash keygen (prefixState s) steps cycles calls blocks t)
    (returned : t.pc = 0x1014) :
    Executes hash keygen s (steps + 24)
      ⟨.success, Expansion.finishState (outputCopied t), cycles + 24, calls, blocks⟩ := by
  have result := (prefix_block s pc).trace.trans tree
  simpa [Execution.charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    result.then_executes (finish hash t returned)

/-- info: 'SigGolfCandidate.Hypertree.Keygen.finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish

end SigGolfCandidate.Hypertree.Keygen
end

namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource
set_option maxRecDepth 4096

/-- Full exact keygen execution, with the reference public key in the organizer's output buffer. -/
theorem executes (hash : Hash) (secretKey : SecretKey) :
    ∃ final, Executes hash keygen (secretKeyState secretKey) 77097 ⟨.success,final,82446,739,761⟩ ∧
      ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64 := by
  obtain ⟨root,treeTrace,treePC,treeSP,words⟩ :=
    KeygenTree.execute hash (prefixState (secretKeyState secretKey)) (prefix_pc _ (secretKey_pc secretKey))
      (by rw [prefix_sp,secretKey_sp]) 159 0 secretKey (by decide) (prefix_context secretKey)
  have returned : root.pc=0x1014 := by rw [treePC,prefix_ra _ (secretKey_pc secretKey)]; decide
  refine ⟨Expansion.finishState (outputCopied root),
    executes_of_tree_trace hash (secretKeyState secretKey) root (secretKey_pc secretKey) 77073 82422 739 761 treeTrace returned,?_⟩
  intro i
  fin_cases i
  · rw [finish_mem]
    exact words 0
  · rw [finish_mem]
    exact words 1

theorem decode_publicKey (hash : Hash) (secretKey : SecretKey) (final : MachineState)
    (words : ∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
      (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) :
    readBuffer final 0x40 16=Reference.keygen hash secretKey := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [Signing.getByte_word final 0x40 i (by decide) (by omega),words ⟨i/8,by omega⟩]
  exact KeygenNode.extractByte_slice (Reference.keygen hash secretKey) i

/-- The exact submitted keygen program returns the functional reference public key for every oracle and secret key. -/
theorem run_refines (hash : Hash) (secretKey : SecretKey) :
    ∃ cache : Cache, submission.runWith hash .keygen secretKey=
      ⟨some (Reference.keygen hash secretKey,cache),true,82446,739,761⟩ := by
  obtain ⟨final,trace,words⟩ := executes hash secretKey
  have run := runWith_of_executes submission hash .keygen secretKey (secretKeyState secretKey) 77097
    ⟨.success,final,82446,739,761⟩ (secretKey_loaded secretKey) trace (by decide)
  refine ⟨readBuffer final 0x60 CACHE_BYTES,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x40 16,readBuffer final 0x60 CACHE_BYTES),true,82446,739,761⟩ :
    RunResult (PublicKey×Cache)) = _
  rw [decode_publicKey hash secretKey final words]
  rfl

/-- Public-key-only formulation of the machine/reference correspondence. -/
theorem publicKey (hash : Hash) (secretKey : SecretKey) :
    ((submission.runWith hash .keygen secretKey).value.map Prod.fst)=some (Reference.keygen hash secretKey) := by
  obtain ⟨cache,run⟩ := run_refines hash secretKey
  rw [run]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenFunctional.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refines

end SigGolfCandidate.Hypertree.KeygenFunctional


namespace SigGolfCandidate.Hypertree.KeygenFunctional
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp Keygen KeygenResource
set_option maxRecDepth 4096

/-- The candidate's public cache contains no secret key-dependent state. -/
def zeroCache : Cache := 0

theorem decode_zero_cache (s : MachineState)
    (zero : ∀ a : Word, 0x60 ≤ a.toNat → a.toNat < 0x80000 → s.getMem a=0) :
    readBuffer s 0x60 CACHE_BYTES=zeroCache := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  have hi' : i < 131072 := hi
  rw [Signing.getByte_word s 0x60 i (by decide) (by omega)]
  have lower : 0x60 ≤ (Signing.wordAddress 0x60 (i/8)).toNat := by
    change 0x60 ≤ (0x60+8*(i/8))%2^64
    omega
  have upper : (Signing.wordAddress 0x60 (i/8)).toNat < 0x80000 := by
    change (0x60+8*(i/8))%2^64 < 0x80000
    omega
  rw [zero _ lower upper]
  simp [zeroCache, extractByte]

theorem executes_zero_cache (hash : Hash) (secretKey : SecretKey) :
    ∃ final, Executes hash keygen (secretKeyState secretKey) 77097 ⟨.success,final,82446,739,761⟩ ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress 0x40 i.val)=
        (Reference.keygen hash secretKey).extractLsb' (64*i.val) 64) ∧
      readBuffer final 0x60 CACHE_BYTES=zeroCache := by
  obtain ⟨root,treeTrace,treePC,treeSP,words,frame⟩ :=
    KeygenTree.execute_framed hash (prefixState (secretKeyState secretKey)) (prefix_pc _ (secretKey_pc secretKey))
      (by rw [prefix_sp,secretKey_sp]) 159 0 secretKey (by decide) (prefix_context secretKey)
  have returned : root.pc=0x1014 := by rw [treePC,prefix_ra _ (secretKey_pc secretKey)]; decide
  refine ⟨Expansion.finishState (outputCopied root),
    executes_of_tree_trace hash (secretKeyState secretKey) root (secretKey_pc secretKey) 77073 82422 739 761 treeTrace returned,?_,?_⟩
  · intro i
    fin_cases i
    · rw [finish_mem]; exact words 0
    · rw [finish_mem]; exact words 1
  · apply decode_zero_cache
    intro a lower upper
    have h40 : a ≠ 0x40 := by intro eq; rw [eq] at lower; change 0x60 ≤ 0x40 at lower; omega
    have h48 : a ≠ 0x48 := by intro eq; rw [eq] at lower; change 0x60 ≤ 0x48 at lower; omega
    have hl : a ≠ 0x80400 := by intro eq; rw [eq] at upper; change 0x80400 < 0x80000 at upper; omega
    rw [finish_mem,if_neg h48,if_neg h40,frame a upper,prefix_mem,if_neg hl]
    exact secretKey_zero secretKey a (by omega)

/-- Exact typed key generation, including its canonical zero cache. -/
theorem run_exact (hash : Hash) (secretKey : SecretKey) :
    submission.runWith hash .keygen secretKey =
      ⟨some (Reference.keygen hash secretKey,zeroCache),true,82446,739,761⟩ := by
  obtain ⟨final,trace,words,cache⟩ := executes_zero_cache hash secretKey
  have run := runWith_of_executes submission hash .keygen secretKey (secretKeyState secretKey) 77097
    ⟨.success,final,82446,739,761⟩ (secretKey_loaded secretKey) trace (by decide)
  rw [run]
  change (⟨some (readBuffer final 0x40 16,readBuffer final 0x60 CACHE_BYTES),true,82446,739,761⟩ :
    RunResult (PublicKey×Cache)) = _
  rw [decode_publicKey hash secretKey final words,cache]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.KeygenFunctional.run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_exact

end SigGolfCandidate.Hypertree.KeygenFunctional
