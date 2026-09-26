import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Loaded67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedWire67
import SigGolfCandidate.Hypertree.KeygenDomain
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Setup67

/-! The verifier's first H2 query is the reference bottom-leaf hash. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Semantic67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem query_eq (s : MachineState) (index : Nat)
    (seed : Reference.Digest)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 384)
    (head : s.getMem 0x80000 = KeygenDomain.header 2 0 0 0 0)
    (indexWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 index).extractLsb' (64*i.val) 64)
    (seedWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64) :
    hashInput s = SecurityRandomOracle.addressedInput
      2 0 index 0 0 0 (bytes seed) := by
  have words := KeygenDomain.words_of_layout s
    (KeygenDomain.header 2 0 0 0 0) index seed
    head indexWords seedWords
  rw [KeygenDomain.query_eq s _ index seed source bits words]
  rfl

theorem answer_words (hash : Hash) (query final : MachineState)
    (index : Nat) (seed : Reference.Digest)
    (queryInput : hashInput query = SecurityRandomOracle.addressedInput
      2 0 index 0 0 0 (bytes seed))
    (stored : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80500 i.val) =
        (hash (hashInput query)).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80500 i.val) =
        (GroupedBottomTree.leafFromSeed hash index seed).extractLsb'
          (64*i.val) 64 := by
  intro i
  rw [stored i,queryInput]
  change (hash (SecurityRandomOracle.addressedInput
      2 0 index 0 0 0 (bytes seed))).extractLsb' (64*i.val) 64 =
    ((hash (SecurityRandomOracle.addressedInput
      2 0 index 0 0 0 (bytes seed))).extractLsb' 0 128).extractLsb'
      (64*i.val) 64
  exact (BitVec.extractLsb'_extractLsb'_of_le (by
    have hi := i.isLt
    omega)).symm

theorem seed_words_of_pair (s : MachineState) (seed : Reference.Digest)
    (pair : s.getMem 0x80028 ++ s.getMem 0x80020 = seed) :
    ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        seed.extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · have low :
        (s.getMem 0x80028 ++ s.getMem 0x80020).extractLsb' 0 64 =
          s.getMem 0x80020 := by bv_decide
    rw [pair] at low
    simpa [Signing.wordAddress] using low.symm
  · have high :
        (s.getMem 0x80028 ++ s.getMem 0x80020).extractLsb' 64 64 =
          s.getMem 0x80028 := by bv_decide
    rw [pair] at high
    simpa [Signing.wordAddress] using high.symm

theorem index_words_of_packed (s : MachineState) (index : Nat)
    (packed : ((s.getMem 0x80018 ++ s.getMem 0x80010 ++
      s.getMem 0x80008) : BitVec 192).toNat = index) :
    ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 index).extractLsb' (64*i.val) 64 := by
  let bits : BitVec 192 :=
    s.getMem 0x80018 ++ s.getMem 0x80010 ++ s.getMem 0x80008
  have bitsNat : bits.toNat = index := packed
  have bitsEq : bits = BitVec.ofNat 192 index := by
    apply BitVec.eq_of_toNat_eq
    have bound : index < 2^192 := by
      rw [← bitsNat]
      exact bits.isLt
    rw [bitsNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
  intro i
  fin_cases i
  · have low : bits.extractLsb' 0 64 = s.getMem 0x80008 := by
      dsimp [bits]
      bv_decide
    rw [bitsEq] at low
    simpa [Signing.wordAddress] using low.symm
  · have mid : bits.extractLsb' 64 64 = s.getMem 0x80010 := by
      dsimp [bits]
      bv_decide
    rw [bitsEq] at mid
    simpa [Signing.wordAddress] using mid.symm
  · have high : bits.extractLsb' 128 64 = s.getMem 0x80018 := by
      dsimp [bits]
      bv_decide
    rw [bitsEq] at high
    simpa [Signing.wordAddress] using high.symm

#print axioms query_eq
#print axioms answer_words
#print axioms seed_words_of_pair
#print axioms index_words_of_packed
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH2Semantic67
