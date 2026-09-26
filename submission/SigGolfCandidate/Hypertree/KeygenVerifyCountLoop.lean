import SigGolfCandidate.Hypertree.VerifyLeafLoop

/-! Inlined from SigGolfCandidate.Hypertree.KeygenVerifyCount; its only importer was SigGolfCandidate.Hypertree.KeygenVerifyCountLoop. -/
section
namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

def chainPrefix (message : Reference.Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (7-(Reference.digit message ⟨i%46, Nat.mod_lt _ (by decide)⟩).val)

theorem chainPrefix_zero (message : Reference.Digest) : chainPrefix message 0=0 := by simp [chainPrefix]

theorem chainPrefix_succ (message : Reference.Digest) (n : Nat) (bound : n<46) :
    chainPrefix message (n+1)=chainPrefix message n+(7-(Reference.digit message ⟨n,bound⟩).val) := by
  simp [chainPrefix,Finset.sum_range_succ,Nat.mod_eq_of_lt bound]

def chainCalls (message : Reference.Digest) : Nat := ∑ chain : Reference.Chain, (7-(Reference.digit message chain).val)

theorem chainPrefix_full (message : Reference.Digest) : chainPrefix message 46=chainCalls message := by
  unfold chainCalls chainPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.mod_eq_of_lt i.isLt]

end SigGolfCandidate.Hypertree.KeygenVerifyCount
end

namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem chainPrefixFast_eq (message : Reference.Digest) (count : Nat) :
    Verifying.chainPrefixFast message count = chainPrefix message count := rfl

theorem recover_all_chains_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (small : level < 160)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 33166 ∧ cycles ≤ 35420 ∧ calls ≤ 322 ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, OutsideLeafWork a → final.getMem a = s.getMem a) ∧ calls = chainCalls message := by
  obtain ⟨final,steps,cycles,calls,run,stepCycle,cycleBound,callBound,
    exactCalls,finalPC,finalCounter,finalData,endpoints,finalRA,finalSP,frame⟩ :=
    Verifying.recover_all_chains_fast hash s level tree side base message values
      small pc data counter aligned bound
  have exact : calls = chainCalls message := by
    rw [exactCalls,chainPrefixFast_eq,chainPrefix_full]
  exact ⟨final,steps,cycles,calls,run,by omega,by omega,by omega,
    finalPC,finalCounter,finalData,endpoints,finalRA,finalSP,frame,exact⟩

end SigGolfCandidate.Hypertree.KeygenVerifyCount
