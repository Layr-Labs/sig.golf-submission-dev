import SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyFrame67

/-! Exact copied word contents for the repeated upper Merkle copy loops. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

theorem run_copy_words (hash : Hash) (s : MachineState)
    (p : Word) (src dst count : BitVec 12)
    (source destination total : Nat)
    (setup : SetupCode image p src dst count)
    (loop : Keygen.CopyCode image (p+20))
    (pc : s.pc = p)
    (sourceReg : (setupState s src dst count).getReg .x6 =
      BitVec.ofNat 64 source)
    (destinationReg : (setupState s src dst count).getReg .x7 =
      BitVec.ofNat 64 destination)
    (countReg : (setupState s src dst count).getReg .x10 =
      BitVec.ofNat 64 total)
    (positive : 0 < total) (size : total ≤ 2097152)
    (sourceBound : source + 8*total ≤ MEMORY_BYTES)
    (destinationBound : destination + 8*total ≤ MEMORY_BYTES)
    (sourceAlign : source % 8 = 0)
    (destinationAlign : destination % 8 = 0)
    (separate : source + 8*total ≤ destination ∨
      destination + 8*total ≤ source) :
    ∃ final,
      Trace hash image s (5+6*total) (5+6*total) 0 0 final ∧
      Keygen.CopyInvariant (p+20) source destination total 0 final ∧
      (∀ i, i < total →
        final.getMem (Signing.wordAddress destination i) =
          s.getMem (Signing.wordAddress source i)) ∧
      (∀ a, (∀ i, i < total →
        a ≠ Signing.wordAddress destination i) →
        final.getMem a = s.getMem a) := by
  let prepared := setupState s src dst count
  have first := setup_block p src dst count setup s pc
  have inv : Keygen.CopyInvariant (p+20) source destination total total
      prepared := by
    refine ⟨Nat.le_refl _,size,?_,?_,?_,countReg⟩
    · simp [positive.ne',prepared,setup_pc,pc]
    · simpa using sourceReg
    · simpa using destinationReg
  obtain ⟨final,second,done,words,frame⟩ := Signing.copy_all image (p+20)
    loop source destination total prepared inv sourceBound destinationBound
    sourceAlign destinationAlign separate
  refine ⟨final,?_,done,?_,?_⟩
  · have path := (OrdinarySteps.trace (hash := hash) first).trans
      (OrdinarySteps.trace (hash := hash) second)
    simpa [prepared,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using path
  · intro i hi
    rw [words i hi]
    exact GroupedBalancedByteFastCopyFrame67.setup_mem s src dst count _
  · intro a outside
    rw [frame a outside]
    exact GroupedBalancedByteFastCopyFrame67.setup_mem s src dst count a

#print axioms run_copy_words

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67
