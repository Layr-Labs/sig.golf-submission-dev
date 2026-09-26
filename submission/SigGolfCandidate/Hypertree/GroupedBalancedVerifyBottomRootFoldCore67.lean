import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootAt67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFold67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRoundInputs67

/-! A resource-bounded ten-round induction for the bottom verifier root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootFoldCore67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide

def RootWords (s : MachineState) (root : Reference.Digest) : Prop :=
  ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x80500 i.val) =
      root.extractLsb' (64*i.val) 64

def RootState (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (initial start s : MachineState) (k : Nat) : Prop :=
  s.pc = GroupedBalancedVerifyTreeH4Fold67.loopPC k ∧
  s.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt k ∧
  s.getMem 0x81050 = GroupedBalancedVerifyTreeH4Fold67.countAt k ∧
  s.getMem 0x81000 = start.getMem 0x81000 + BitVec.ofNat 64 k ∧
  GroupedBalancedVerifyH4IndexHeader67.StoredIndex s (wide index >>> k) ∧
  GroupedBalancedVerifyStackGlobal67.LowFrame initial s ∧
  SafeFrame start s ∧
  RootWords s (GroupedBalancedVerifyBottomRootAt67.rootAt
    hash index witness k)

def RoundStep (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (initial start : MachineState) : Prop :=
  ∀ k : Nat, k < 10 → ∀ s : MachineState,
    RootState hash index witness initial start s k →
    ∃ m t, (m = 162 ∨ m = 163) ∧
      Trace hash image s m (m+7) 1 1 t ∧
      RootState hash index witness initial start t (k+1)

theorem rounds_of_step (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (initial start : MachineState)
    (startState : RootState hash index witness initial start start 0)
    (step : RoundStep hash index witness initial start) :
    ∀ k : Nat, k ≤ 10 →
      ∃ n final, n ≤ 163*k ∧
        Trace hash image start n (n+7*k) k k final ∧
        RootState hash index witness initial start final k := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨0,start,by decide,?_,startState⟩
      simpa using (Trace.refl start : Trace hash image start 0 0 0 0 start)
  | succ k ih =>
      intro hk
      obtain ⟨n,mid,nBound,run,midState⟩ := ih (by omega)
      obtain ⟨m,final,mCases,roundRun,finalState⟩ :=
        step k (by omega) mid midState
      refine ⟨n+m,final,?_,?_,finalState⟩
      · rcases mCases with h | h <;> omega
      · have all := run.trans roundRun
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
          Nat.mul_add,Nat.add_mul] using all

#print axioms rounds_of_step
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootFoldCore67
