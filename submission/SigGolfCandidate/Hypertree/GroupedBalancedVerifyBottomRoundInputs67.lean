import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomWireSiblings67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Fold67

/-! Machine pointer arithmetic for the ten loaded bottom siblings. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRoundInputs67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyBottomRecoverRecurrence67

theorem pointer_eq (k : Nat) :
    GroupedBalancedVerifyTreeH4Fold67.ptrAt k =
      BitVec.ofNat 64 (0x2c730+16*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [GroupedBalancedVerifyTreeH4Fold67.ptrAt,ih]
      change BitVec.ofNat 64 (0x2c730+16*k) +
        BitVec.ofNat 64 16 = BitVec.ofNat 64 (0x2c730+16*(k+1))
      rw [← BitVec.ofNat_add]
      congr 1

theorem sibling_words (message : Message) (pk : PublicKey)
    (wire : Bytes 50848) (initial s : MachineState)
    (loaded : initialState GroupedBalancedProgram67ByteSign.submission
      .verify (message,pk,wire) = some initial)
    (low : GroupedBalancedVerifyStackGlobal67.LowFrame initial s)
    (k : Nat) (hk : k < 10) :
    ∀ i : Fin 2,
      s.getMem (GroupedBalancedVerifyTreeH4Fold67.ptrAt k +
        BitVec.ofNat 64 (8*i.val)) =
        ((siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
          simpa [siblings_length] using hk)).extractLsb' (64*i.val) 64 := by
  have pair := GroupedBalancedVerifyBottomWireSiblings67.framed_sibling
    message pk wire initial s loaded low k hk
  intro i
  fin_cases i
  · have lo := congrArg (fun v : Reference.Digest => v.extractLsb' 0 64) pair
    have lo' : s.getMem (BitVec.ofNat 64 (0x2c730+16*k)) =
        ((siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
          simpa [siblings_length] using hk)).extractLsb' 0 64 := by
      simpa only [BitVec.extractLsb'_append_eq_right] using lo
    simpa [pointer_eq] using lo'
  · have hi := congrArg (fun v : Reference.Digest => v.extractLsb' 64 64) pair
    have hi' : s.getMem (BitVec.ofNat 64 (0x2c730+16*k+8)) =
        ((siblings (GroupedBalancedWire67.decode wire).bottom)[k]'(by
          simpa [siblings_length] using hk)).extractLsb' 64 64 := by
      simpa only [BitVec.extractLsb'_append_eq_left] using hi
    have addr : GroupedBalancedVerifyTreeH4Fold67.ptrAt k + (8 : Word) =
        BitVec.ofNat 64 (0x2c730+16*k+8) := by
      rw [pointer_eq]
      change BitVec.ofNat 64 (0x2c730+16*k) + BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add]
    change s.getMem (GroupedBalancedVerifyTreeH4Fold67.ptrAt k + 8) = _
    rw [addr]
    exact hi'

#print axioms pointer_eq
#print axioms sibling_words
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRoundInputs67
