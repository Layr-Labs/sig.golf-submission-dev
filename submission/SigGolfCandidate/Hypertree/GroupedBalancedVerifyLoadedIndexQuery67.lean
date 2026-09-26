import SigGolfCandidate.Hypertree.GroupedBalancedVerifyPrefixIndex67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyReferenceBridge67
import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Output67

/-! The loaded direct67 verifier's first H5 query is the reference index query. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67ByteSign.submission
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem initial_message (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial) :
    ∀ i, i < 32 →
      initial.getByte (BitVec.ofNat 64 i) =
        message.extractLsb' (8*i) 8 := by
  intro i hi
  have h := GroupedBalancedVerifyReferenceBridge67.initial_message_byte
    message pk wire initial loaded i hi
  simpa only [bytes,List.getElem_map,List.getElem_range] using h

theorem initial_randomizer (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial) :
    ∀ i, i < 32 →
      initial.getByte (BitVec.ofNat 64 (0x2c700+i)) =
        (GroupedBalancedWire67.decode wire).randomizer.extractLsb' (8*i) 8 := by
  intro i hi
  have h := GroupedBalancedVerifyReferenceBridge67.initial_wire_byte
    message pk wire initial loaded i (by omega)
  simp only [bytes,List.getElem_map,List.getElem_range] at h
  change initial.getByte (BitVec.ofNat 64 (0x2c700+i)) =
    (wire.extractLsb' 0 256).extractLsb' (8*i) 8
  rw [h]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  simp only [BitVec.getLsbD_extractLsb',
    show 8*i+bit < 256 by omega,decide_true,Bool.true_and,
    show 8*i+bit < 8*50848 by omega]
  simp only [Nat.zero_add]

theorem loaded_query (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ query,
      Trace hash image initial 104 104 0 0 query ∧
      query.pc = 0x1110 ∧
      query.getReg .x5 = 1 ∧
      query.getReg .x10 = 0x80000 ∧
      query.getReg .x11 = 896 ∧
      query.getReg .x12 = 0x80300 ∧
      hashInput query = SecurityRandomOracle.indexInput message
        (GroupedBalancedWire67.decode wire).randomizer ∧
      query.getMem 0x81048 = 0x2c720 := by
  exact GroupedBalancedVerifyPrefixIndex67.h5_query_refines hash initial
    message (GroupedBalancedWire67.decode wire).randomizer pc
    (initial_message message pk wire initial loaded)
    (initial_randomizer message pk wire initial loaded)

private theorem copy_code : Keygen.CopyCode image 0x1128 := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code Keygen.CopyCode
  decide

theorem copy_index_answer (s : MachineState) (pc : s.pc = 0x1114) :
    ∃ final, OrdinarySteps image s 17 final ∧ final.pc = 0x1140 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          s.getMem (Signing.wordAddress 0x80300 i.val)) ∧
      final.getMem 0x80310 = s.getMem 0x80310 ∧
      final.getMem 0x81048 = s.getMem 0x81048 := by
  let setup := GroupedBalancedVerifyH5Output67.copySetup s
  have setupRun := GroupedBalancedVerifyH5Output67.setup_steps s pc
  have setupPC := GroupedBalancedVerifyH5Output67.setup_pc s pc
  obtain ⟨src,dst,count⟩ := GroupedBalancedVerifyH5Output67.setup_regs s
  have inv : Keygen.CopyInvariant 0x1128 0x80300 0x81008 2 2 setup := by
    simp [Keygen.CopyInvariant,setup,setupPC,src,dst,count]
  obtain ⟨final,copyRun,done,words,frame,_,_⟩ :=
    Keygen.copy_all_frame image 0x1128 copy_code
      0x80300 0x81008 2 setup inv
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_,_,endPC,_,_,_⟩ := done
  refine ⟨final,?_,by simpa using endPC,?_,?_,?_⟩
  · simpa only [Nat.reduceAdd] using
      Keygen.ordinary_trans image s setup final 5 12 setupRun copyRun
  · intro i
    exact (words i.val i.isLt).trans
      (GroupedBalancedVerifyH5Output67.setup_mem s _)
  · exact (frame 0x80310 (by intro i hi; interval_cases i <;> decide)).trans
      (GroupedBalancedVerifyH5Output67.setup_mem s 0x80310)
  · exact (frame 0x81048 (by intro i hi; interval_cases i <;> decide)).trans
      (GroupedBalancedVerifyH5Output67.setup_mem s 0x81048)

theorem loaded_low_words (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000) :
    ∃ final,
      Trace hash image initial 122 137 1 2 final ∧
      final.pc = 0x1140 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x81008 i.val) =
          (hash (SecurityRandomOracle.indexInput message
            (GroupedBalancedWire67.decode wire).randomizer)).extractLsb'
            (64*i.val) 64) ∧
      final.getMem 0x80310 =
        (hash (SecurityRandomOracle.indexInput message
          (GroupedBalancedWire67.decode wire).randomizer)).extractLsb'
            128 64 ∧
      final.getMem 0x81048 = 0x2c720 := by
  obtain ⟨query,before,queryPC,service,src,len,dst,queryInput,pointer⟩ :=
    loaded_query hash message pk wire initial loaded pc
  have valid : hashArgumentsValid query = true :=
    Keygen.hash_arguments query 896 src (by simpa using len) dst
      (by decide)
  have hcomp : compressions (hashInput query).1 = 2 := by
    have hlen : (hashInput query).1 = 896 := by
      simp [hashInput,len,BitVec.toNat_ofNat]
    rw [hlen]
    decide
  let answer := hash (hashInput query)
  let afterHash := writeHash query answer
  have hashRun : Trace hash image query 1 16 1 2 afterHash := by
    have code : Keygen.instructionAt image 0x1110 =
        some (.base .ECALL) := by
      unfold image GroupedBalancedVerifyImage67Fast2Byte.image
        GroupedBalancedVerifyImage67Fast2Byte.code
      decide
    have fetchCode : fetch image query = some (.base .ECALL) := by
      simpa only [Keygen.fetch_at,queryPC] using code
    have raw := Trace.hash query afterHash 0 0 0 0 fetchCode
      service valid (Trace.refl afterHash)
    simpa [hcomp,afterHash] using raw
  have afterPC : afterHash.pc = 0x1114 := by
    simpa [afterHash,answer,Keygen.hash_pc,queryPC] using
      Keygen.hash_pc query answer
  obtain ⟨final,copyRun,finalPC,words,highFrame,pointerFrame⟩ :=
    copy_index_answer afterHash afterPC
  refine ⟨final,?_,finalPC,?_,?_,?_⟩
  · have all := before.trans (hashRun.trans copyRun.trace)
    simpa only [Nat.reduceAdd] using all
  · intro i
    have copied := words i
    have result := Signing.hash_answer_word query answer dst
      (⟨i.val,by have h := i.isLt; omega⟩ : Fin 4)
    have result' : afterHash.getMem
        (Signing.wordAddress 0x80300 i.val) =
        (hash (hashInput query)).extractLsb' (64*i.val) 64 := by
      simpa [afterHash,answer] using result
    rw [queryInput] at result'
    exact copied.trans result'
  · have result := Signing.hash_answer_word query answer dst
      (⟨2,by decide⟩ : Fin 4)
    have result' : afterHash.getMem 0x80310 =
        (hash (hashInput query)).extractLsb' 128 64 := by
      simpa [afterHash,answer,Signing.wordAddress] using result
    rw [queryInput] at result'
    exact highFrame.trans result'
  · have hashPointer : afterHash.getMem 0x81048 = query.getMem 0x81048 := by
      exact Signing.hash_answer_frame query answer dst 0x81048
        (by intro i; fin_cases i <;> decide)
    exact pointerFrame.trans (hashPointer.trans pointer)

#print axioms loaded_query
#print axioms loaded_low_words
#print axioms copy_index_answer
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexQuery67
