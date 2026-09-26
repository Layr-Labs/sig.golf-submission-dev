import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67

/-! The table decoder never changes its public lookup data. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTableFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCompose67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCopyLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteCopyMem67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTail67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem table_bit20 (i : Nat) (hi : i < 2304) :
    (BitVec.ofNat 64 (0xfff700+i)).getLsbD 20 = true := by
  rw [BitVec.getLsbD_ofNat]
  simp only [show decide (20 < 64) = true by decide, Bool.true_and]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : (0xfff700+i) / 2^20 = 15 := by omega
  rw [hdiv]
  decide

private theorem output_bit20 (n : Nat) (hn : n < 16) :
    (BitVec.ofNat 64 (0x80600+4*n)).getLsbD 20 = false := by
  rw [BitVec.getLsbD_ofNat]
  simp only [show decide (20 < 64) = true by decide, Bool.true_and]
  exact Nat.testBit_lt_two_pow (by omega : 0x80600+4*n < 2^20)

private theorem aligned_bit20 (a : Word) :
    (alignToDword a).getLsbD 20 = a.getLsbD 20 := by
  simp [alignToDword]

private theorem table_copy_separate (i n : Nat) (hi : i < 2304)
    (hn : n < 16) :
    alignToDword (BitVec.ofNat 64 (0xfff700+i)) ≠
      alignToDword (BitVec.ofNat 64 (0x80600+4*n)) := by
  intro h
  have hb := congrArg (fun v : Word => v.getLsbD 20) h
  rw [aligned_bit20, aligned_bit20, table_bit20 i hi,
    output_bit20 n hn] at hb
  cases hb

theorem copyLoop_table_byte (s : MachineState) (n : Nat)
    (hn : n ≤ 16) (output : s.getReg .x11 = 0x80600)
    (i : Nat) (hi : i < 2304) :
    (copyLoop s n).getByte (BitVec.ofNat 64 (0xfff700+i)) =
      s.getByte (BitVec.ofNat 64 (0xfff700+i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    have hptr : (copyLoop s n).getReg .x11 =
        BitVec.ofNat 64 (0x80600+4*n) := by
      rw [copyLoop_output_pointer, output, BitVec.ofNat_add]
      rfl
    have hne : alignToDword (BitVec.ofNat 64 (0xfff700+i)) ≠
        alignToDword ((copyLoop s n).getReg .x11) := by
      rw [hptr]
      exact table_copy_separate i n hi hn1
    change (GroupedBalancedVerifyByteCopy67.copyBody (copyLoop s n)).getByte _ = _
    rw [copyBody_preserves_byte _ _ hne, ih hn0]

#print axioms copyLoop_table_byte

theorem postSum_table_byte (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a88)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (output : s.getReg .x11 = 0x80600)
    (i : Nat) (hi : i < 2304) :
    (postSumState s message).getByte (BitVec.ofNat 64 (0xfff700+i)) =
      s.getByte (BitVec.ofNat 64 (0xfff700+i)) := by
  let a : Word := BitVec.ofNat 64 (0xfff700+i)
  let b := selectedBranch s message
  let c := copyLoop b 16
  have hfield := selectedBranch_fields s message pc sum stack
  have hb11 : b.getReg .x11 = 0x80600 := by
    rcases hfield with ⟨_,_,_,_,_,hx11,_⟩
    rw [hx11, output]
  have hc11 : c.getReg .x11 = 0x80640 := by
    rw [copyLoop_output_pointer, hb11]
    decide
  have ha_bit : a.getLsbD 20 = true := table_bit20 i hi
  have hbflag : a ≠ s.getReg .x11 + 64 := by
    rw [output]
    intro h
    have ht := congrArg (fun v : Word => v.getLsbD 20) h
    rw [ha_bit] at ht
    have hf : ((0x80600 : Word) + 64).getLsbD 20 = false := by decide
    rw [hf] at ht
    cases ht
  have htail1 : a ≠ c.getReg .x11 + 1 := by
    rw [hc11]
    intro h
    have ht := congrArg (fun v : Word => v.getLsbD 20) h
    rw [ha_bit] at ht
    have hf : ((0x80640 : Word) + 1).getLsbD 20 = false := by decide
    rw [hf] at ht
    cases ht
  have htail2 : a ≠ c.getReg .x11 + 2 := by
    rw [hc11]
    intro h
    have ht := congrArg (fun v : Word => v.getLsbD 20) h
    rw [ha_bit] at ht
    have hf : ((0x80640 : Word) + 2).getLsbD 20 = false := by decide
    rw [hf] at ht
    cases ht
  change (tailState c).getByte a = s.getByte a
  rw [tail_preserves_other c a htail1 htail2]
  rw [copyLoop_table_byte b 16 (by decide) hb11 i hi]
  exact selectedBranch_preserves_byte s message a hbflag

#print axioms postSum_table_byte

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTableFrame67
