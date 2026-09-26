import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInnerTickData67

/-! One parent address increment with a certified low-word no-carry bound. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressStep67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private theorem div64 (address : Nat)
    (noCarry : address % 18446744073709551616 + 1 < 18446744073709551616) :
    (address + 1) / 18446744073709551616 =
      address / 18446744073709551616 := by
  omega

private theorem div128 (address : Nat)
    (noCarry : address % 18446744073709551616 + 1 < 18446744073709551616) :
    (address + 1) / 340282366920938463463374607431768211456 =
      address / 340282366920938463463374607431768211456 := by
  have hmod : (address % 340282366920938463463374607431768211456) %
      18446744073709551616 = address % 18446744073709551616 := by omega
  omega

theorem low_step (address : Nat) (h : address < 2^160)
    (noCarry : address % 18446744073709551616 + 1 < 18446744073709551616) :
    (BitVec.ofNat 192 (address+1)).extractLsb' 0 64 =
      (BitVec.ofNat 192 address).extractLsb' 0 64 + 1 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,BitVec.toNat_add,
    Nat.shiftRight_zero]
  have h192 : address+1 < 2^192 := by omega
  have h192b : address < 2^192 := by omega
  rw [Nat.mod_eq_of_lt h192,Nat.mod_eq_of_lt h192b]
  have hone : (1 : BitVec 64).toNat = 1 := rfl
  rw [hone]
  omega

theorem middle_step (address : Nat) (h : address < 2^160)
    (noCarry : address % 18446744073709551616 + 1 < 18446744073709551616) :
    (BitVec.ofNat 192 (address+1)).extractLsb' 64 64 =
      (BitVec.ofNat 192 address).extractLsb' 64 64 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  have hh := div64 address noCarry
  omega

theorem high_step (address : Nat) (h : address < 2^160)
    (noCarry : address % 18446744073709551616 + 1 < 18446744073709551616) :
    (BitVec.ofNat 192 (address+1)).extractLsb' 128 64 =
      (BitVec.ofNat 192 address).extractLsb' 128 64 := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  have hh := div128 address noCarry
  omega

#print axioms low_step
#print axioms middle_step
#print axioms high_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressStep67


/-! Alignment of each bottom-tree parent level prevents low-word carry while another parent remains. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentNoCarry67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem no_carry (base height n : Nat)
    (heightBound : height < 10)
    (aligned : base % (512 / 2^height) = 0)
    (next : n+1 < 512 / 2^height) :
    (base+n) % 18446744073709551616 + 1 < 18446744073709551616 := by
  interval_cases height <;> norm_num at *
  all_goals omega

#print axioms no_carry
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentNoCarry67

/-! Three-word H4 address invariant across a signing parent tick. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem tick_address_words (hash : Hash) (s : MachineState)
    (count target tree : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (countBound : count < 512)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (treeBound : tree < 2^160)
    (noCarry : tree % 18446744073709551616 + 1 < 18446744073709551616)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem
        (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 (tree+1)).extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · change (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem
      0x81008 = _
    have h0 : s.getMem 0x81008 = (BitVec.ofNat 192 tree).extractLsb' 0 64 := by
      simpa [Signing.wordAddress] using address (0 : Fin 3)
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_address hash s count target
      counter destination countBound targetCase,h0]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.low_step
      tree treeBound noCarry).symm
  · change (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem
      0x81010 = _
    have h1 : s.getMem 0x81010 = (BitVec.ofNat 192 tree).extractLsb' 64 64 := by
      simpa [Signing.wordAddress] using address (1 : Fin 3)
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame hash s
      count target 0x81010 counter destination countBound targetCase
      (by decide) (by decide) (by decide) (by decide),h1]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.middle_step
      tree treeBound noCarry).symm
  · change (GroupedBalancedSignBottomTreeInnerTickFrame67.tickState hash s).getMem
      0x81018 = _
    have h2 : s.getMem 0x81018 = (BitVec.ofNat 192 tree).extractLsb' 128 64 := by
      simpa [Signing.wordAddress] using address (2 : Fin 3)
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame hash s
      count target 0x81018 counter destination countBound targetCase
      (by decide) (by decide) (by decide) (by decide),h2]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.high_step
      tree treeBound noCarry).symm

#print axioms tick_address_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressData67
