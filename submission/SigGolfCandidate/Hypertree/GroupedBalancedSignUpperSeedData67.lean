import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEvenData67


/-! The machine's low-bit branch agrees with the chain's parity. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedParity67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

theorem parity_word (chain : Nat) :
    (BitVec.ofNat 64 chain &&& (1 : Word)) =
      BitVec.ofNat 64 (chain%2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change chain % 2^64 &&& 1 = chain%2%2^64
  rw [show (1:Nat)=2^1-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  norm_num
  omega

theorem even_bit (chain : Fin 67) (parity : chain.val%2=0) :
    (BitVec.ofNat 64 chain.val &&& (1 : Word))=0 := by
  rw [parity_word,parity]
  decide

theorem odd_bit (chain : Fin 67) (parity : chain.val%2=1) :
    (BitVec.ofNat 64 chain.val &&& (1 : Word))≠0 := by
  rw [parity_word,parity]
  decide

#print axioms parity_word
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedParity67


/-! One parity-independent chain seed handoff, including the H1 pair cache. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem seed (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67) (s : MachineState)
    (pc : s.pc=0x1760)
    (chainWord : s.getMem 0x81030=BitVec.ofNat 64 chain.val)
    (level : s.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (cached : chain.val%2=1 → ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val)=
        (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
          (chain.val/2)).extractLsb' (128+64*i.val) 64) :
    ∃ final : MachineState,
      Trace hash image s
        (if chain.val%2=0 then 127 else 26)
        (if chain.val%2=0 then 134 else 26)
        (if chain.val%2=0 then 1 else 0)
        (if chain.val%2=0 then 1 else 0) final ∧
      final.pc=0x18e8 ∧
      final.getReg .x19=BitVec.ofNat 64 chain.val ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val)=
          (GroupedBalancedUpperTree67.secret hash secretKey base leaf
            chain).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80d10 i.val)=
          (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
            (chain.val/2)).extractLsb' (128+64*i.val) 64) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        final.getMem a=s.getMem a) := by
  by_cases parity : chain.val%2=0
  · have evenBit : s.getMem 0x81030 &&& (1 : Word)=0 := by
      rw [chainWord]
      exact GroupedBalancedSignUpperSeedParity67.even_bit chain parity
    obtain ⟨final,path,done,chainReg,stack,seedWords,cache,frame,middle,
      low,digitFrame⟩ :=
      GroupedBalancedSignUpperSeedEvenData67.even_seed hash secretKey
        base leaf chain s pc chainWord parity evenBit level address keyWords
    exact ⟨final,by simpa [parity] using path,done,chainReg,stack,
      seedWords,cache,frame,middle,low,digitFrame⟩
  · have odd : chain.val%2=1 := by omega
    have oddBit : s.getMem 0x81030 &&& (1 : Word)≠0 := by
      rw [chainWord]
      exact GroupedBalancedSignUpperSeedParity67.odd_bit chain odd
    obtain ⟨final,path,done,chainReg,stack,seedWords,cache,frame,middle,
      low,digitFrame⟩ :=
      GroupedBalancedSignUpperSeedOddData67.odd_seed hash secretKey
        base leaf chain s pc chainWord odd oddBit (cached odd)
    refine ⟨final,by simpa [parity] using path,done,chainReg,stack,
      seedWords,?_,frame,middle,low,digitFrame⟩
    intro i
    rw [cache i]
    exact cached odd i

#print axioms seed
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedData67
