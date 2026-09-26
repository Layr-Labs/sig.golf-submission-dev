import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexRound67

/-! All ten H4 rounds shift the 192-bit tree index right by ten bits. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
open GroupedBalancedVerifyH4IndexHeader67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

private theorem pointer_valid (k : Nat) (h : k < 10) :
    accessValid (GroupedBalancedVerifyTreeH4Fold67.ptrAt k) 8 = true ∧
    accessValid (GroupedBalancedVerifyTreeH4Fold67.ptrAt k + 8) 8 = true := by
  interval_cases k <;> decide

private theorem pc_next (k : Nat) (h : k < 10) :
    (if GroupedBalancedVerifyTreeH4Fold67.countAt k + 1 ≠ (10 : Word)
      then 0x1290 else 0x14f4) =
      GroupedBalancedVerifyTreeH4Fold67.loopPC (k+1) := by
  interval_cases k <;> decide

private theorem shift_assoc (index : BitVec 192) (k : Nat) :
    (index >>> k) >>> 1 = index >>> (k+1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, pow_succ]

theorem rounds_index (hash : Hash) (start : MachineState)
    (index : BitVec 192)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0)
    (stored : StoredIndex start index) :
    ∀ k : Nat, k ≤ 10 →
      ∃ n final, n ≤ 163*k ∧
        Trace hash image start n (n+7*k) k k final ∧
        final.pc = GroupedBalancedVerifyTreeH4Fold67.loopPC k ∧
        final.getMem 0x81048 =
          GroupedBalancedVerifyTreeH4Fold67.ptrAt k ∧
        final.getMem 0x81050 =
          GroupedBalancedVerifyTreeH4Fold67.countAt k ∧
        SafeFrame start final ∧ StoredIndex final (index >>> k) ∧
        final.getMem 0x81000 =
          start.getMem 0x81000 + BitVec.ofNat 64 k ∧
        GroupedBalancedVerifyStackGlobal67.LowFrame start final := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨0,start,by decide,?_,?_,?_,?_,safe_refl start,?_,?_,
        GroupedBalancedVerifyStackGlobal67.LowFrame.refl start⟩
      · simpa using (Trace.refl start : Trace hash image start 0 0 0 0 start)
      · simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using pc
      · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using pointer
      · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using counter
      · simpa using stored
      · simp
  | succ k ih =>
      intro hk
      have klt : k < 10 := by omega
      obtain ⟨n,mid,nBound,run,midPC,midPointer,midCounter,midSafe,
        midIndex,midBase,midLow⟩ := ih (by omega)
      have roundPC : mid.pc = 0x1290 := by
        simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC,
          Nat.ne_of_lt klt] using midPC
      obtain ⟨m,final,mCases,roundRun,endPointer,endCounter,endPC,
        roundSafe,roundIndex,roundBase,roundLow⟩ :=
        GroupedBalancedVerifyH4IndexRound67.round_index hash mid
          (GroupedBalancedVerifyTreeH4Fold67.ptrAt k)
          (GroupedBalancedVerifyTreeH4Fold67.countAt k)
          (index >>> k) roundPC midPointer midCounter
          (pointer_valid k klt).1 (pointer_valid k klt).2 midIndex
      refine ⟨n+m,final,?_,?_,?_,?_,?_,safe_trans midSafe roundSafe,?_,?_,
        midLow.trans roundLow⟩
      · rcases mCases with h | h <;> omega
      · have all := run.trans roundRun
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
          Nat.mul_add,Nat.add_mul] using all
      · rw [endPC]
        exact pc_next k klt
      · simpa [GroupedBalancedVerifyTreeH4Fold67.ptrAt] using endPointer
      · simpa [GroupedBalancedVerifyTreeH4Fold67.countAt] using endCounter
      · simpa only [shift_assoc] using roundIndex
      · calc
          final.getMem 0x81000 = mid.getMem 0x81000 + 1 := roundBase
          _ = (start.getMem 0x81000 + BitVec.ofNat 64 k) + 1 := by rw [midBase]
          _ = start.getMem 0x81000 + BitVec.ofNat 64 (k+1) := by
            simp [BitVec.ofNat_add,BitVec.add_assoc]

theorem ten_rounds_index (hash : Hash) (start : MachineState)
    (index : BitVec 192)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0)
    (stored : StoredIndex start index) :
    ∃ n final, n ≤ 1630 ∧
      Trace hash image start n (n+70) 10 10 final ∧
      final.pc = 0x14f4 ∧
      final.getMem 0x81048 = GroupedBalancedVerifyTreeH4Fold67.ptrAt 10 ∧
      final.getMem 0x81050 = GroupedBalancedVerifyTreeH4Fold67.countAt 10 ∧
      SafeFrame start final ∧ StoredIndex final (index >>> 10) ∧
      final.getMem 0x81000 = start.getMem 0x81000 + 10 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame start final := by
  obtain ⟨n,final,bound,run,endPC,endPointer,endCount,safe,endIndex,
    endBase,low⟩ :=
    rounds_index hash start index pc pointer counter stored 10 (by decide)
  exact ⟨n,final,by simpa using bound,by simpa using run,
    by simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC] using endPC,
    endPointer,endCount,safe,endIndex,by simpa using endBase,low⟩

#print axioms ten_rounds_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexFold67
