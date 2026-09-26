import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootFoldCore67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4RoundUnique67

/-! A functional H4 round and the indexed H4 round describe one final state. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
open GroupedBalancedVerifyBottomRootFoldCore67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide

def RootRound (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (initial start : MachineState) : Prop :=
  ∀ k : Nat, k < 10 → ∀ s : MachineState,
    RootState hash index witness initial start s k →
    ∃ m t, (m = 162 ∨ m = 163) ∧
      Trace hash image s m (m+7) 1 1 t ∧
      t.pc =
        (if GroupedBalancedVerifyTreeH4Fold67.countAt k + 1 ≠ (10 : Word)
          then 0x1290 else 0x14f4) ∧
      RootWords t (GroupedBalancedVerifyBottomRootAt67.rootAt
        hash index witness (k+1))

private theorem pointer_valid (k : Nat) (hk : k < 10) :
    accessValid (GroupedBalancedVerifyTreeH4Fold67.ptrAt k) 8 = true ∧
    accessValid (GroupedBalancedVerifyTreeH4Fold67.ptrAt k + 8) 8 = true := by
  interval_cases k <;> decide

private theorem shift_assoc (index : BitVec 192) (k : Nat) :
    (index >>> k) >>> 1 = index >>> (k+1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul,pow_succ]

theorem roundStep_of_rootRound (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (initial start : MachineState)
    (functional : RootRound hash index witness initial start) :
    RoundStep hash index witness initial start := by
  intro k hk s state
  have inputState := state
  obtain ⟨pc,pointer,counter,base,stored,low,safe,root⟩ := state
  obtain ⟨m,fromRoot,mCases,rootRun,rootPC,rootWords⟩ :=
    functional k hk s inputState
  have roundPC : s.pc = 0x1290 := by
    have kNe : k ≠ 10 := Nat.ne_of_lt hk
    simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC,kNe] using pc
  obtain ⟨n,fromIndex,nCases,indexRun,nextPointer,nextCounter,
    nextPC,roundSafe,nextIndex,nextBase,roundLow⟩ :=
    GroupedBalancedVerifyH4IndexRound67.round_index hash s
      (GroupedBalancedVerifyTreeH4Fold67.ptrAt k)
      (GroupedBalancedVerifyTreeH4Fold67.countAt k)
      (wide index >>> k) roundPC
      pointer counter (pointer_valid k hk).1 (pointer_valid k hk).2 stored
  obtain ⟨sameN,sameFinal⟩ :=
    GroupedBalancedVerifyH4RoundUnique67.round_unique hash s
      fromRoot fromIndex (GroupedBalancedVerifyTreeH4Fold67.countAt k)
      m n (m+7) (n+7) 1 1 1 1 mCases nCases
      rootRun indexRun rootPC nextPC
  have combinedRoot : RootWords fromIndex
      (GroupedBalancedVerifyBottomRootAt67.rootAt
        hash index witness (k+1)) := by
    rw [← sameFinal]
    exact rootWords
  refine ⟨n,fromIndex,nCases,indexRun,?_,?_,?_,?_,?_,?_,?_,combinedRoot⟩
  · rw [nextPC]
    interval_cases k <;> decide
  · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using nextPointer
  · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using nextCounter
  · calc
      fromIndex.getMem 0x81000 = s.getMem 0x81000 + 1 := nextBase
      _ = (start.getMem 0x81000 + BitVec.ofNat 64 k) + 1 := by rw [base]
      _ = start.getMem 0x81000 + BitVec.ofNat 64 (k+1) := by
        simp [BitVec.ofNat_add,BitVec.add_assoc]
  · simpa only [shift_assoc] using nextIndex
  · exact low.trans roundLow
  · exact safe_trans safe roundSafe

#print axioms roundStep_of_rootRound
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootStep67
