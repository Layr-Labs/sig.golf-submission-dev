import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Round67

/-! Execute all ten verifier H4 tree rounds. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Fold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyTreeHighFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67Byte.submission

def ptrAt : Nat → Word
  | 0 => 0x2c730
  | k+1 => ptrAt k + 16

def countAt : Nat → Word
  | 0 => 0
  | k+1 => countAt k + 1

def loopPC (k : Nat) : Word := if k = 10 then 0x14f4 else 0x1290

private theorem pointer_valid (k : Nat) (h : k < 10) :
    accessValid (ptrAt k) 8 = true ∧
    accessValid (ptrAt k + 8) 8 = true := by
  interval_cases k <;> decide

private theorem pc_next (k : Nat) (h : k < 10) :
    (if countAt k + 1 ≠ (10 : Word) then 0x1290 else 0x14f4) =
      loopPC (k+1) := by
  interval_cases k <;> decide

theorem rounds (hash : Hash) (start : MachineState)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0) :
    ∀ k : Nat, k ≤ 10 →
      ∃ n final, n ≤ 163*k ∧
        Trace hash image start n (n+7*k) k k final ∧
        final.pc = loopPC k ∧
        final.getMem 0x81048 = ptrAt k ∧
        final.getMem 0x81050 = countAt k ∧
        SafeFrame start final := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨0,start,by decide,?_,?_,?_,?_,safe_refl start⟩
      · simpa using (Trace.refl start : Trace hash image start 0 0 0 0 start)
      · simpa [loopPC] using pc
      · simpa [ptrAt] using pointer
      · simpa [countAt] using counter
  | succ k ih =>
      intro hk
      have klt : k < 10 := by omega
      obtain ⟨n,mid,nBound,run,midPC,midPointer,midCounter,midSafe⟩ := ih (by omega)
      have roundPC : mid.pc = 0x1290 := by
        simpa [loopPC, Nat.ne_of_lt klt] using midPC
      obtain ⟨m,final,mCases,roundRun,endPointer,endCounter,endPC,roundSafe⟩ :=
        GroupedBalancedVerifyTreeH4Round67.round hash mid (ptrAt k) (countAt k)
          roundPC midPointer midCounter (pointer_valid k klt).1 (pointer_valid k klt).2
      refine ⟨n+m,final,?_,?_,?_,?_,?_,safe_trans midSafe roundSafe⟩
      · rcases mCases with h | h <;> omega
      · have all := run.trans roundRun
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
          Nat.mul_add,Nat.add_mul] using all
      · rw [endPC]
        exact pc_next k klt
      · simpa [ptrAt] using endPointer
      · simpa [countAt] using endCounter

theorem ten_rounds (hash : Hash) (start : MachineState)
    (pc : start.pc = 0x1290)
    (pointer : start.getMem 0x81048 = 0x2c730)
    (counter : start.getMem 0x81050 = 0) :
    ∃ n final, n ≤ 1630 ∧
      Trace hash image start n (n+70) 10 10 final ∧
      final.pc = 0x14f4 ∧
      final.getMem 0x81048 = ptrAt 10 ∧
      final.getMem 0x81050 = countAt 10 ∧
      SafeFrame start final := by
  obtain ⟨n,final,bound,run,endPC,endPointer,endCount,safe⟩ :=
    rounds hash start pc pointer counter 10 (by decide)
  exact ⟨n,final,by simpa using bound,by simpa using run,
    by simpa [loopPC] using endPC,endPointer,endCount,safe⟩

theorem loaded_tree (hash : Hash) (input : Input program.sizes .verify) :
    ∃ initial n final,
      initialState program .verify input = some initial ∧
      n ≤ 1848 ∧
      Trace hash image initial n (n+92) 12 13 final ∧
      final.pc = 0x14f4 ∧
      final.getMem 0x81048 = ptrAt 10 ∧
      final.getMem 0x81050 = countAt 10 := by
  obtain ⟨initial,start,loaded,startRun,startPC,pointer,counter⟩ :=
    GroupedBalancedVerifyTreeStart67.loaded_start hash input
  obtain ⟨n,final,nBound,roundRun,endPC,endPointer,endCounter,_⟩ :=
    ten_rounds hash start startPC pointer counter
  refine ⟨initial,218+n,final,loaded,by omega,?_,endPC,endPointer,endCounter⟩
  have run := startRun.trans roundRun
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

#print axioms ten_rounds
#print axioms loaded_tree
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Fold67
