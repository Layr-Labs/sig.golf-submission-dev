import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointStore67


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperEndpointStore67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem store_values (s : MachineState) (chain : Nat)
    (h : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (bound : chain < 67) :
    ∀ j : Fin 2,
      (storeState s).getMem (Signing.wordAddress (0x80800+16*chain) j.val) =
        s.getMem (Signing.wordAddress 0x80020 j.val) := by
  have addr := address_eq s chain h
  have next : address s + 8 = BitVec.ofNat 64 (0x80800+16*chain+8) := by
    rw [addr]
    exact (BitVec.ofNat_add _ _).symm
  have addrNat : (address s).toNat = 0x80800+16*chain := by
    rw [addr]
    have small : 0x80800+16*chain < 18446744073709551616 := by omega
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have nextNat : (address s + 8).toNat = 0x80800+16*chain+8 := by
    rw [next]
    have small : 0x80800+16*chain+8 < 18446744073709551616 := by omega
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have noCounter0 : address s ≠ 0x81030 := by
    intro eq
    have he := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat] at he
    omega
  have noCounter1 : address s + 8 ≠ 0x81030 := by
    intro eq
    have he := congrArg BitVec.toNat eq
    simp [BitVec.toNat_ofNat] at he
    omega
  have distinct : address s ≠ address s + 8 := by
    intro eq
    have he := congrArg BitVec.toNat eq
    rw [addrNat,nextNat] at he
    omega
  intro j
  fin_cases j
  · change (storeState s).getMem (BitVec.ofNat 64 (0x80800+16*chain)) =
      s.getMem 0x80020
    rw [←addr,store_mem]
    simp [noCounter0,distinct]
    intro e
    exact False.elim (noCounter0 e)
  · change (storeState s).getMem (BitVec.ofNat 64 (0x80800+16*chain+8)) =
      s.getMem 0x80028
    rw [←next,store_mem]
    simp [noCounter1]
    intro e
    exact False.elim (noCounter1 e)

#print axioms store_values
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointData67


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointControl67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree GroupedBalancedSignUpperEndpointStore67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem store_counter_eq (s : MachineState) (chain : Nat)
    (h : s.getMem 0x81030 = BitVec.ofNat 64 chain) :
    (storeState s).getMem 0x81030 = BitVec.ofNat 64 (chain+1) := by
  rw [store_mem]
  simpa [h,BitVec.ofNat_add]

theorem store_pc_chain (s : MachineState) (chain : Nat)
    (pc : s.pc = 0x1ab0)
    (h : s.getMem 0x81030 = BitVec.ofNat 64 chain)
    (bound : chain < 67) :
    (storeState s).pc = if chain+1=67 then 0x1afc else 0x1760 := by
  rw [store_pc,pc,h]
  have one : BitVec.ofNat 64 chain + 1 = BitVec.ofNat 64 (chain+1) := by
    simpa using (BitVec.ofNat_add chain 1).symm
  rw [one]
  by_cases last : chain+1=67
  · rw [if_pos last]
    rw [last]
    decide
  · rw [if_neg last]
    have notWord : BitVec.ofNat 64 (chain+1) ≠ (67 : Word) := by
      intro eq
      have he := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : chain+1<2^64)] at he
      omega
    rw [if_neg notWord]
    decide



#print axioms store_pc_chain
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperEndpointControl67
