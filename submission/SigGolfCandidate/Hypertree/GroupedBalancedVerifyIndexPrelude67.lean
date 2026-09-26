import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexQuery67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Prelude67

/-! The third H5 answer word is masked to the 160-bit path index. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexPrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

theorem index_words (s : MachineState) :
    (GroupedBalancedVerifyH2Prelude67.preludeState s).getMem 0x81008 =
      s.getMem 0x81008 ∧
    (GroupedBalancedVerifyH2Prelude67.preludeState s).getMem 0x81010 =
      s.getMem 0x81010 ∧
    (GroupedBalancedVerifyH2Prelude67.preludeState s).getMem 0x81018 =
      ((s.getMem 0x80310 <<< 32) >>> 32) := by
  simp [GroupedBalancedVerifyH2Prelude67.preludeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem index_split_nat (answer : BitVec 256) :
    (((answer.extractLsb' 128 64 <<< 32) >>> 32) ++
      answer.extractLsb' 64 64 ++ answer.extractLsb' 0 64).toNat =
      (answer.extractLsb' 0 160).toNat := by
  have bits : (((answer.extractLsb' 128 64 <<< 32) >>> 32) ++
      answer.extractLsb' 64 64 ++ answer.extractLsb' 0 64) =
      (answer.extractLsb' 0 160).zeroExtend 192 := by
    apply BitVec.eq_of_getLsbD_eq
    intro bit hbit
    simp only [BitVec.getLsbD_append,BitVec.zeroExtend_eq_setWidth,
      BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft]
    have hb192 : bit < 192 := by omega
    by_cases h64 : bit < 64
    · have h160 : bit < 160 := by omega
      simp [h64,h160,hb192]
    by_cases h128 : bit < 128
    · have h160 : bit < 160 := by omega
      have sub : bit-64 < 64 := by omega
      have eq : 64+(bit-64)=bit := by omega
      simp [h64,h128,h160,hb192,sub,eq]
    by_cases h160 : bit < 160
    · have sub : ¬bit-64 < 64 := by omega
      have sub2 : bit-64-64 < 64 := by omega
      have mask : 32+(bit-64-64) < 64 := by omega
      have eq : 128+(bit-64-64)=bit := by omega
      simp [h64,h128,h160,hb192,sub,sub2,mask,eq]
    · have sub : ¬bit-64 < 64 := by omega
      have mask : ¬32+(bit-64-64) < 64 := by omega
      simp [h64,h128,h160,hb192,sub,mask]
  calc
    _ = ((answer.extractLsb' 0 160).zeroExtend 192).toNat :=
      congrArg BitVec.toNat bits
    _ = (answer.extractLsb' 0 160).toNat := by
      simpa only [BitVec.zeroExtend_eq_setWidth] using
        (BitVec.toNat_setWidth_of_le
          (b := answer.extractLsb' 0 160) (w' := 192) (by decide))

theorem loaded_prelude_index (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ final,
      Trace hash GroupedBalancedVerifyImage67Fast2Byte.image
        initial 139 154 1 2 final ∧
      final.pc = 0x1184 ∧
      final.getMem 0x81048 = 0x2c720 ∧
      ((final.getMem 0x81018 ++ final.getMem 0x81010 ++
        final.getMem 0x81008) : BitVec 192).toNat =
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer).toNat := by
  obtain ⟨before,prefixRun,pcBefore,lowWords,third,pointer⟩ :=
    GroupedBalancedVerifyLoadedIndexQuery67.loaded_low_words
      hash message pk wire initial loaded pc
  let final := GroupedBalancedVerifyH2Prelude67.preludeState before
  have prelude := GroupedBalancedVerifyH2Prelude67.prelude_steps
    before pcBefore pointer
  obtain ⟨low,high,top⟩ := index_words before
  refine ⟨final,?_,GroupedBalancedVerifyH2Prelude67.prelude_pc
    before pcBefore,(GroupedBalancedVerifyH2Prelude67.prelude_sibling
      before pointer).2.2,?_⟩
  · simpa only [Nat.reduceAdd] using prefixRun.trans prelude.trace
  · rw [low,high,top]
    have low0 : before.getMem 0x81008 =
        (hash (SecurityRandomOracle.indexInput message
          (GroupedBalancedWire67.decode wire).randomizer)).extractLsb' 0 64 := by
      simpa [Signing.wordAddress] using lowWords 0
    have low1 : before.getMem 0x81010 =
        (hash (SecurityRandomOracle.indexInput message
          (GroupedBalancedWire67.decode wire).randomizer)).extractLsb' 64 64 := by
      simpa [Signing.wordAddress] using lowWords 1
    rw [low0,low1,third]
    have refEq : Reference.indexOf hash message
        (GroupedBalancedWire67.decode wire).randomizer =
        (hash (SecurityRandomOracle.indexInput message
          (GroupedBalancedWire67.decode wire).randomizer)).extractLsb' 0 160 := rfl
    rw [refEq]
    exact index_split_nat (hash (SecurityRandomOracle.indexInput message
      (GroupedBalancedWire67.decode wire).randomizer))

#print axioms index_words
#print axioms index_split_nat
#print axioms loaded_prelude_index
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyIndexPrelude67
