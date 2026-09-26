import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedEntryRootConditional67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4FunctionalRound67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRoundValue67

/-! The concrete H4 machine round computes the bottom witness recurrence. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRound67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyBottomRootFoldCore67
open GroupedBalancedVerifyBottomRootStep67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide
private abbrev ptrAt := GroupedBalancedVerifyTreeH4Fold67.ptrAt
private abbrev countAt := GroupedBalancedVerifyTreeH4Fold67.countAt
private abbrev rootAt := GroupedBalancedVerifyBottomRootAt67.rootAt
private abbrev siblings (witness : GroupedBottomTree.Witness 10) :=
  GroupedBalancedVerifyBottomRecoverRecurrence67.siblings witness

private theorem pointer_small (k : Nat) (hk : k < 10) :
    (ptrAt k).toNat < 0x80000 ∧ (ptrAt k + 8).toNat < 0x80000 ∧
      accessValid (ptrAt k) 8 = true ∧
      accessValid (ptrAt k + 8) 8 = true := by
  interval_cases k <;> decide

theorem loaded_root_round (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848) :
    GroupedBalancedVerifyLoadedEntryRootConditional67.LoadedRootRound
      hash message pk wire := by
  intro initial start loaded startRun
  let index := Reference.indexOf hash message
    (GroupedBalancedWire67.decode wire).randomizer
  let witness := (GroupedBalancedWire67.decode wire).bottom
  have startBase :=
    (GroupedBalancedVerifyLoadedStartRoot67.start_fields
      hash message pk wire initial start loaded startRun).1
  intro k hk s state
  obtain ⟨pc,pointer,counter,base,stored,low,_,rootWords⟩ := state
  have loopPC : s.pc = 0x1290 := by
    simpa [GroupedBalancedVerifyTreeH4Fold67.loopPC, Nat.ne_of_lt hk] using pc
  have levelWord : s.getMem 0x81000 = BitVec.ofNat 64 k := by
    rw [base,startBase]
    simp
  have siblingWords :=
    GroupedBalancedVerifyBottomRoundInputs67.sibling_words
      message pk wire initial s loaded low k hk
  obtain ⟨pSmall,p8Small,valid0,valid8⟩ := pointer_small k hk
  obtain ⟨n,t,nCases,run,_,_,finalPC,_,_,_,_,finalRoot⟩ :=
    GroupedBalancedVerifyH4FunctionalRound67.round_root hash s
      (ptrAt k) (countAt k) (wide index >>> k) k
      (rootAt hash index witness k)
      ((siblings witness)[k]'(by
        simpa [GroupedBalancedVerifyBottomRecoverRecurrence67.siblings_length]
          using hk))
      loopPC pointer counter pSmall p8Small valid0 valid8 stored
      levelWord rootWords siblingWords
  have lowWord : s.getMem (0x81008#64) =
      (wide index >>> k).extractLsb' 0 64 := by
    have h := stored (0 : Fin 3)
    change s.getMem (0x81008#64) =
      (wide index >>> k).extractLsb' 0 64 at h
    exact h
  have words : RootWords t (rootAt hash index witness (k+1)) := by
    intro i
    have h := finalRoot i
    rw [lowWord] at h
    have nodeEq :
        Reference.node hash k (((wide index >>> k) >>> 1).toNat)
          (if (wide index >>> k).extractLsb' 0 64 &&& 1#64 = 0#64
            then rootAt hash index witness k
            else (siblings witness)[k]'(by
              simpa [GroupedBalancedVerifyBottomRecoverRecurrence67.siblings_length]
                using hk))
          (if (wide index >>> k).extractLsb' 0 64 &&& 1#64 = 0#64
            then (siblings witness)[k]'(by
              simpa [GroupedBalancedVerifyBottomRecoverRecurrence67.siblings_length]
                using hk)
            else rootAt hash index witness k) =
          rootAt hash index witness (k+1) :=
      GroupedBalancedVerifyBottomRootRoundValue67.round_value
        hash index witness k hk
    rw [nodeEq] at h
    exact h
  exact ⟨n,t,nCases,run,finalPC,words⟩

#print axioms loaded_root_round
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRound67
