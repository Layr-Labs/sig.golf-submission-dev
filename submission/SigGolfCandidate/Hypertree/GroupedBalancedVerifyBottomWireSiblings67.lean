import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRecoverRecurrence67

/-! The loaded bottom authentication path is the decoded wire sibling list. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomWireSiblings67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree Reference SignatureEncoding
open GroupedBalancedVerifyBottomRecoverRecurrence67
set_option maxRecDepth 8192

theorem siblings_bottomWitness (wire : Bytes 50848) (height : Nat) :
    siblings (GroupedBalancedWireWitness67.bottomWitness wire height 32) =
      (List.range height).map (fun k => slice wire (32+16*(k+1)) 16) := by
  induction height with
  | zero => rfl
  | succ height ih =>
      simp only [GroupedBalancedWireWitness67.bottomWitness, siblings, ih,
        List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem decoded_sibling (wire : Bytes 50848) (k : Nat) (hk : k < 10) :
    (siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
      simpa only [GroupedBalancedWire67.decode, siblings_length] using hk) =
        slice wire (48+16*k) 16 := by
  simp only [GroupedBalancedWire67.decode, siblings_bottomWitness,
    List.getElem_map, List.getElem_range]
  congr 1
  omega

theorem decoded_seed (wire : Bytes 50848) :
    (GroupedBalancedWire67.decode wire).bottom.seedValue =
      slice wire 32 16 := by
  rfl

theorem loaded_seed (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial) :
    initial.getMem (BitVec.ofNat 64 (0x2c720+8)) ++
      initial.getMem (BitVec.ofNat 64 0x2c720) =
        (GroupedBalancedWire67.decode wire).bottom.seedValue := by
  simpa only [show 0x2c720+8 = 0x2c700+32+8 by decide,
    show 0x2c720 = 0x2c700+32 by decide] using
      (GroupedBalancedVerifyLoadedWire67.initial_digest message pk wire
        initial loaded 32 (by decide) (by decide)).trans
        (decoded_seed wire).symm

theorem framed_seed (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a) :
    entry.getMem (BitVec.ofNat 64 (0x2c720+8)) ++
      entry.getMem (BitVec.ofNat 64 0x2c720) =
        (GroupedBalancedWire67.decode wire).bottom.seedValue := by
  rw [frame _ (by decide), frame _ (by decide)]
  exact loaded_seed message pk wire initial loaded

theorem loaded_sibling (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (k : Nat) (hk : k < 10) :
    initial.getMem (BitVec.ofNat 64 (0x2c730+16*k+8)) ++
      initial.getMem (BitVec.ofNat 64 (0x2c730+16*k)) =
        (siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
          simpa only [GroupedBalancedWire67.decode, siblings_length] using hk) := by
  have loadedDigest := GroupedBalancedVerifyLoadedWire67.initial_digest
    message pk wire initial loaded (48+16*k) (by omega) (by omega)
  simpa only [show 0x2c730+16*k+8 = 0x2c700+(48+16*k)+8 by omega,
    show 0x2c730+16*k = 0x2c700+(48+16*k) by omega] using
      loadedDigest.trans (decoded_sibling wire k hk).symm

theorem framed_sibling (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial entry : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (frame : ∀ a : Word, a.toNat < 0x80000 →
      entry.getMem a = initial.getMem a)
    (k : Nat) (hk : k < 10) :
    entry.getMem (BitVec.ofNat 64 (0x2c730+16*k+8)) ++
      entry.getMem (BitVec.ofNat 64 (0x2c730+16*k)) =
        (siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
          simpa only [GroupedBalancedWire67.decode, siblings_length] using hk) := by
  rw [frame _ (by simp only [BitVec.toNat_ofNat]; omega),
    frame _ (by simp only [BitVec.toNat_ofNat]; omega)]
  exact loaded_sibling message pk wire initial loaded k hk

#print axioms siblings_bottomWitness
#print axioms decoded_sibling
#print axioms loaded_seed
#print axioms framed_seed
#print axioms loaded_sibling
#print axioms framed_sibling
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomWireSiblings67
