import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroupFinish67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRootMatch67

/-! A verified final path enters the public-key comparison and terminates. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalPath67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem final_path_executes (hash : Hash) (s mid : MachineState)
    (steps cycles calls blocks : Nat)
    (root pk : Reference.Digest)
    (run : Trace hash image s steps cycles calls blocks mid)
    (pc : mid.pc = 0x19c4)
    (group : mid.getMem 0x81058 = 44)
    (rootWords : ∀ i : Fin 2,
      mid.getMem (BitVec.ofNat 64 (0x80500+8*i.val)) =
        root.extractLsb' (64*i.val) 64)
    (pkWords : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (0x40+8*i.val)) =
        pk.extractLsb' (64*i.val) 64)
    (lowFrame : ∀ a : Word, a.toNat < 0x80000 →
      mid.getMem a = s.getMem a) :
    ∃ (extra : Nat) (final : MachineState), extra ≤ 27 ∧
      Executes hash image s (steps+extra)
        ⟨if root = pk then .success else .failure,
          final, cycles+extra, calls, blocks⟩ := by
  have midPk : ∀ i : Fin 2,
      mid.getMem (BitVec.ofNat 64 (0x40+8*i.val)) =
        pk.extractLsb' (64*i.val) 64 := by
    intro i
    rw [lowFrame _ (by fin_cases i <;> decide)]
    exact pkWords i
  have matchRoot := GroupedBalancedVerifyRootMatch67.root_matches_iff
    mid root pk rootWords midPk
  obtain ⟨extra,final,bound,suffix,_⟩ :=
    GroupedBalancedVerifyEndGroupFinish67.final_group_executes
      hash mid pc group
  have combined := run.then_executes suffix
  refine ⟨extra,final,bound,?_⟩
  simpa [Execution.charge,matchRoot] using combined

#print axioms final_path_executes
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyFinalPath67
