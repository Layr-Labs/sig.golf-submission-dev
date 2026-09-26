import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.GroupedBalancedWire67
import SigGolfCandidate.Memory

/-! Relate the loaded verifier witness buffer to the parsed direct67 signature. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyReferenceBridge67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem initial_wire_byte (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some s)
    (i : Nat) (hi : i < 50848) :
    s.getByte (BitVec.ofNat 64 (0x2c700+i)) =
      (bytes wire)[i]'(by simpa using hi) := by
  simp only [initialState,
    if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  rw [SigGolfCandidate.Memory.getByte_setReg]
  dsimp only [inputBuffers,List.foldl_cons,List.foldl_nil,
    program,GroupedBalancedProgram67ByteSign.submission,
    GroupedBalancedProgram67.sizes,Riscv.standardLayout,
    Riscv.witnessBase,Riscv.signatureBase]
  have hwbase : BitVec.ofNat 64 (131168+8*((50848+7)/8)) =
      (0x2c700 : Word) := by decide
  rw [hwbase]
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let d := blank.writeBytesAsWords
    (BitVec.ofNat 64
      (Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image))
    GroupedBalancedVerifyImage67Fast2Byte.image.data
  let m := d.writeBytesAsWords 0 (bytes message)
  let t := m.writeBytesAsWords 0x40 (bytes pk)
  change (t.writeBytesAsWords (BitVec.ofNat 64 0x2c700)
    (bytes wire)).getByte (BitVec.ofNat 64 (0x2c700+i)) = _
  exact SigGolfCandidate.Memory.write_byte t 0x2c700
    (bytes wire) i (by decide)
    (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by rw [SigGolfCandidate.Memory.bytes_length];
        exact hi)

theorem initial_pk_byte (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some s)
    (i : Nat) (hi : i < 16) :
    s.getByte (BitVec.ofNat 64 (0x40+i)) =
      (bytes pk)[i]'(by simpa using hi) := by
  simp only [initialState,
    if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  rw [SigGolfCandidate.Memory.getByte_setReg]
  dsimp only [inputBuffers,List.foldl_cons,List.foldl_nil,
    program,GroupedBalancedProgram67ByteSign.submission,
    GroupedBalancedProgram67.sizes,Riscv.standardLayout,
    Riscv.witnessBase,Riscv.signatureBase]
  have hwbase : BitVec.ofNat 64 (131168+8*((50848+7)/8)) =
      (0x2c700 : Word) := by decide
  rw [hwbase]
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let d := blank.writeBytesAsWords
    (BitVec.ofNat 64
      (Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image))
    GroupedBalancedVerifyImage67Fast2Byte.image.data
  let m := d.writeBytesAsWords 0 (bytes message)
  let t := m.writeBytesAsWords 0x40 (bytes pk)
  change (t.writeBytesAsWords (BitVec.ofNat 64 0x2c700)
    (bytes wire)).getByte (BitVec.ofNat 64 (0x40+i)) = _
  rw [SigGolfCandidate.Memory.write_preserves_byte t 0x2c700
    (bytes wire) 0x40 i (by decide)
    (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (Or.inl (by omega))]
  exact SigGolfCandidate.Memory.write_byte m 0x40
    (bytes pk) i (by decide)
    (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by rw [SigGolfCandidate.Memory.bytes_length]; exact hi)

theorem initial_message_byte (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (s : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some s)
    (i : Nat) (hi : i < 32) :
    s.getByte (BitVec.ofNat 64 i) =
      (bytes message)[i]'(by simpa using hi) := by
  simp only [initialState,
    if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  rw [SigGolfCandidate.Memory.getByte_setReg]
  dsimp only [inputBuffers,List.foldl_cons,List.foldl_nil,
    program,GroupedBalancedProgram67ByteSign.submission,
    GroupedBalancedProgram67.sizes,Riscv.standardLayout,
    Riscv.witnessBase,Riscv.signatureBase]
  have hwbase : BitVec.ofNat 64 (131168+8*((50848+7)/8)) =
      (0x2c700 : Word) := by decide
  rw [hwbase]
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let d := blank.writeBytesAsWords
    (BitVec.ofNat 64
      (Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image))
    GroupedBalancedVerifyImage67Fast2Byte.image.data
  let m := d.writeBytesAsWords 0 (bytes message)
  let t := m.writeBytesAsWords 0x40 (bytes pk)
  change (t.writeBytesAsWords (BitVec.ofNat 64 0x2c700)
    (bytes wire)).getByte (BitVec.ofNat 64 i) = _
  have hwire :
      (t.writeBytesAsWords (BitVec.ofNat 64 0x2c700)
        (bytes wire)).getByte (BitVec.ofNat 64 i) =
      t.getByte (BitVec.ofNat 64 i) := by
    simpa only [Nat.zero_add] using
      (SigGolfCandidate.Memory.write_preserves_byte t 0x2c700
        (bytes wire) 0 i (by decide)
        (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
        (by omega) (Or.inl (by omega)))
  rw [hwire]
  have hpk :
      (m.writeBytesAsWords (BitVec.ofNat 64 0x40)
        (bytes pk)).getByte (BitVec.ofNat 64 i) =
      m.getByte (BitVec.ofNat 64 i) := by
    simpa only [Nat.zero_add] using
      (SigGolfCandidate.Memory.write_preserves_byte m 0x40
        (bytes pk) 0 i (by decide)
        (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
        (by omega) (Or.inl (by omega)))
  change (m.writeBytesAsWords (BitVec.ofNat 64 0x40)
    (bytes pk)).getByte (BitVec.ofNat 64 i) = _
  rw [hpk]
  have hzero : BitVec.ofNat 64 0 = (0 : Word) := by decide
  simpa only [m,Nat.zero_add,hzero] using
    (SigGolfCandidate.Memory.write_byte d 0
      (bytes message) i (by decide)
      (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
      (by rw [SigGolfCandidate.Memory.bytes_length]; exact hi))

#print axioms initial_wire_byte
#print axioms initial_pk_byte
#print axioms initial_message_byte
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyReferenceBridge67
