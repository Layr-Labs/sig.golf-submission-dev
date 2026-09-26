import SigGolfCandidate.Hypertree.GroupedBalancedSignByteInitialAgree67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedUpperStack67
import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
import SigGolfCandidate.Memory
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoader67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67. -/
section
/-! The official sign loader installs all three byte-decoder tables. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev byteSubmission := GroupedBalancedProgram67ByteSign.submission

private theorem image_data_byte (blank : MachineState) (i : Nat)
    (hi : i < 2304) :
    (blank.writeBytesAsWords
      (BitVec.ofNat 64 (Riscv.dataBase GroupedBalancedSignImage67Byte.image))
      GroupedBalancedSignImage67Byte.image.data).getByte
      (BitVec.ofNat 64 (0xfff700+i)) =
        data[i]'(by rw [data_length]; exact hi) := by
  have hbase : Riscv.dataBase GroupedBalancedSignImage67Byte.image = 0xfff700 :=
    GroupedBalancedSignImage67Byte.data_base
  rw [hbase]
  exact SigGolfCandidate.Memory.write_byte _ 0xfff700 data i
    (by decide) (by rw [data_length]; decide) (by rw [data_length]; exact hi)

theorem initial_data_byte (input : Input byteSubmission.sizes .sign)
    (s : MachineState)
    (loaded : initialState byteSubmission .sign input = some s)
    (i : Nat) (hi : i < 2304) :
    s.getByte (BitVec.ofNat 64 (0xfff700+i)) =
      data[i]'(by rw [data_length]; exact hi) := by
  rcases input with ⟨secretKey,cache,message⟩
  simp only [initialState,
    if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .sign)] at loaded
  cases Option.some.inj loaded
  rw [SigGolfCandidate.Memory.getByte_setReg]
  dsimp only [inputBuffers,List.foldl_cons,List.foldl_nil,
    byteSubmission,GroupedBalancedProgram67ByteSign.submission,
    GroupedBalancedProgram67.sizes,Riscv.standardLayout]
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let d := blank.writeBytesAsWords
    (BitVec.ofNat 64 (Riscv.dataBase GroupedBalancedSignImage67Byte.image))
    GroupedBalancedSignImage67Byte.image.data
  let k := d.writeBytesAsWords 0x20 (bytes secretKey)
  let c := k.writeBytesAsWords 0x60 (bytes cache)
  change (c.writeBytesAsWords 0 (bytes message)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  apply Eq.trans (SigGolfCandidate.Memory.write_preserves_byte c 0 (bytes message)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; simp))
  change (k.writeBytesAsWords 0x60 (bytes cache)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  apply Eq.trans (SigGolfCandidate.Memory.write_preserves_byte k 0x60 (bytes cache)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; rw [SigGolfCandidate.Memory.bytes_length]; decide))
  change (d.writeBytesAsWords 0x20 (bytes secretKey)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  apply Eq.trans (SigGolfCandidate.Memory.write_preserves_byte d 0x20 (bytes secretKey)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; simp))
  exact image_data_byte blank i hi

theorem initial_tables (input : Input byteSubmission.sizes .sign)
    (s : MachineState)
    (loaded : initialState byteSubmission .sign input = some s) :
    GroupedBalancedVerifyByteContract67.Tables s := by
  intro i hi
  exact initial_data_byte input s loaded i hi

#print axioms initial_data_byte
#print axioms initial_tables
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoader67
end

/-! Loaded byte-signing program through the bottom tree and first upper boundary. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedUpper67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem loaded_bottom_to_upper (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial upper : MachineState, ∃ n c : Nat,
      initialState GroupedBalancedProgram67ByteSign.submission .sign
        (secretKey,cache,message) = some initial ∧
      Trace hash GroupedBalancedSignImage67Byte.image initial n c
        3073 3075 upper ∧
      upper.pc = 0x15e0 ∧
      (∀ i : Fin 2,
        upper.getMem (BitVec.ofNat 64 (0x80500+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10
            ((leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)))/1024)).extractLsb'
                (64*i.val) 64) ∧
      upper.getMem 0x81058 = 0 ∧
      upper.getMem 0x81060 = 3 ∧
      upper.getMem 0x810f0 = 0x20130 ∧
      (∀ i : Fin 3,
        upper.getMem (Signing.wordAddress 0x81090 i.val) =
          ((BitVec.ofNat 192 (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat) >>> 10).extractLsb'
              (64*i.val) 64) ∧
      upper.getReg .x2=0xfff700 ∧
      upper.getMem 0x81000=10 ∧
      (∀ i : Fin 4, upper.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat →
        upper.getMem a = initial.getMem a) ∧
      n ≤ 257742 ∧ c ≤ 279269 ∧
      (∀ i : Fin 4,
        upper.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        upper.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) := by
  rw [← GroupedBalancedSignByteInitialAgree67.submission_eq]
  exact GroupedBalancedSignBottomLoadedUpperStack67.loaded_bottom_to_upper
    hash secretKey cache message

#print axioms loaded_bottom_to_upper
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedUpper67


/-! The official loaded signer reaches the first upper-group invariant. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def initialIndex (hash : Hash) (secretKey : SecretKey)
    (message : Message) : BitVec 192 :=
  (BitVec.ofNat 192 (Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)).toNat) >>> 10

def bottomRoot (hash : Hash) (secretKey : SecretKey)
    (message : Message) : BitVec 128 :=
  GroupedBottomTree.root hash secretKey 10
    ((GroupedBalancedSignBottomAddress67.leafIndex
      (Reference.indexOf hash message
        (Reference.randomizer hash secretKey message)))/1024)

theorem initial_index_bound (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    (initialIndex hash secretKey message).toNat < 2^150 := by
  let idx := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  have idxBound : idx.toNat < 2^160 := idx.isLt
  have widened : (BitVec.ofNat 192 idx.toNat).toNat = idx.toNat := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [initialIndex,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rw [widened]
  omega

theorem loaded_boundary (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial upper : MachineState, ∃ n c : Nat,
      initialState GroupedBalancedProgram67ByteSign.submission .sign
        (secretKey,cache,message) = some initial ∧
      Trace hash GroupedBalancedSignImage67Byte.image initial n c
        3073 3075 upper ∧
      Boundary hash secretKey (initialIndex hash secretKey message) 0
        (bottomRoot hash secretKey message) upper ∧
      (initialIndex hash secretKey message).toNat < 2^150 := by
  obtain ⟨initial,upper,n,c,loaded,run,pc,rootWords,layer,height,
    witness,selected,stack,treeWord,keyWords,highFrame,_,_,_,_⟩ :=
    GroupedBalancedSignByteLoadedUpper67.loaded_bottom_to_upper
      hash secretKey cache message
  have initialTables := GroupedBalancedSignByteLoader67.initial_tables
    (secretKey,cache,message) initial loaded
  have upperTables :=
    GroupedBalancedSignUpperBaseToInitial67.tables_of_high_frame
      initial upper initialTables highFrame
  have boundary : Boundary hash secretKey
      (initialIndex hash secretKey message) 0
      (bottomRoot hash secretKey message) upper := by
    refine ⟨pc,?_,?_,?_,?_,?_,?_,stack,keyWords,upperTables⟩
    · simpa using layer
    · simpa [GroupedBalancedSignUpperSchedule67.height] using height
    · simpa [GroupedBalancedSignUpperSchedule67.treeBase,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using treeWord
    · simpa [GroupedBalancedSignUpperSchedule67.currentWitness,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using witness
    · intro w
      simpa [initialIndex,GroupedBalancedSignUpperOuterInvariant67.indexAt,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using selected w
    · exact current_of_root upper (bottomRoot hash secretKey message)
        (by intro w; simpa [bottomRoot] using rootWords w)
  exact ⟨initial,upper,n,c,loaded,run,boundary,
    initial_index_bound hash secretKey message⟩

#print axioms loaded_boundary
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67
