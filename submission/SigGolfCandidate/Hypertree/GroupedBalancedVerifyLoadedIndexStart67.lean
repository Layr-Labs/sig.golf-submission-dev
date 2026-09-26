import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexH267
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2LoadedSemantic67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4IndexStart67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomIndexArithmetic67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeLoadedDecoderSafe67

/-! The loaded verifier enters the H4 loop with the reference H5 index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexStart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide

theorem loaded_start_index (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ start,
      Trace hash image initial 218 240 2 3 start ∧
      start.pc = 0x1290 ∧
      start.getMem 0x81048 = 0x2c730 ∧
      start.getMem 0x81050 = 0 ∧
      GroupedBalancedVerifyH4IndexHeader67.StoredIndex start
        (wide (Reference.indexOf hash message
          (GroupedBalancedWire67.decode wire).randomizer)) := by
  obtain ⟨before,prefixRun,beforePC,indexEq⟩ :=
    GroupedBalancedVerifyLoadedIndexH267.loaded_h2_index
      hash message pk wire initial loaded pc
  obtain ⟨otherInitial,_,otherBefore,otherLoaded,otherRun,_,_,pointer⟩ :=
    GroupedBalancedVerifyH2Loaded67.loaded_output hash (message,pk,wire)
  have loadedByte : initialState GroupedBalancedProgram67Byte.submission
      .verify (message,pk,wire) = some initial := by
    rw [GroupedBalancedVerifyH2LoadedSemantic67.initial_verify_eq]
    exact loaded
  have initialEq : otherInitial = initial := by
    exact Option.some.inj (otherLoaded.symm.trans loadedByte)
  rw [initialEq] at otherRun
  have beforeEq : otherBefore = before := Trace.deterministic otherRun prefixRun
  rw [beforeEq] at pointer
  let index := Reference.indexOf hash message
    (GroupedBalancedWire67.decode wire).randomizer
  have bitsEq : GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex before =
      wide index := by
    apply BitVec.eq_of_toNat_eq
    calc
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex before).toNat =
          index.toNat := indexEq
      _ = (wide index).toNat :=
        (GroupedBalancedVerifyBottomIndexArithmetic67.wide_nat index).symm
  have stored : GroupedBalancedVerifyH4IndexHeader67.StoredIndex before
      (wide index) := by
    rw [← bitsEq]
    exact GroupedBalancedVerifyTreeLoadedDecoderSafe67.current_index_words before
  obtain ⟨startRun,startPC,startPointer,startCounter,startIndex,_⟩ :=
    GroupedBalancedVerifyH4IndexStart67.start_index before (wide index)
      beforePC pointer stored
  refine ⟨GroupedBalancedVerifyTreeStart67.startState before,?_,
    startPC,startPointer,startCounter,startIndex⟩
  simpa only [Nat.reduceAdd] using prefixRun.trans startRun.trace

#print axioms loaded_start_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexStart67
