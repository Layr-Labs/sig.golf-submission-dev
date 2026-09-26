import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSeed67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalChain67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidCopy67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalStep67. -/
section
/-! Each H2 chain changes only its selected endpoint slot in the mid scratch range. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalMidTick67
open GroupedBalancedKeygenLeafFunctionalMidChain67
open GroupedBalancedKeygenEndpointCopy67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem word_ne_of_lt (n limit : Nat)
    (small : n < limit) (limitBound : limit < 2^64) :
    (BitVec.ofNat 64 n : Word) ≠ BitVec.ofNat 64 limit := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2^64),
    Nat.mod_eq_of_lt limitBound] at h
  omega

def OtherSlotFrame (n : Nat) (before after : MachineState) : Prop :=
  ∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d20 →
    (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80800 (2*n+i.val)) →
    after.getMem a = before.getMem a

theorem mid_to_other {s t : MachineState} (n : Nat)
    (frame : MidFrame s t) : OtherSlotFrame n s t := by
  intro a lower upper _
  exact frame a lower upper

theorem copy_other (s : MachineState) (n : Nat) (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n) :
    OtherSlotFrame n s (copyState s) := by
  intro a lower upper outside
  have n0 : a ≠ 0x81030 := by
    intro same
    rw [same] at upper
    exact (by decide : ¬((0x81030 : Word).toNat < 0x80d20)) upper
  have n1 : a ≠ address s := by
    rw [address_eq s n counter]
    have eq : BitVec.ofNat 64 (0x80800+16*n) =
        Signing.wordAddress 0x80800 (2*n) := by
      change BitVec.ofNat 64 (0x80800+16*n) =
        BitVec.ofNat 64 (0x80800+8*(2*n))
      congr 1
      omega
    rw [eq]
    exact outside ⟨0,by decide⟩
  have n2 : a ≠ address s + 8 := by
    rw [address_eq s n counter]
    have eq : BitVec.ofNat 64 (0x80800+16*n) + 8 =
        Signing.wordAddress 0x80800 (2*n+1) := by
      change BitVec.ofNat 64 (0x80800+16*n) + BitVec.ofNat 64 8 =
        BitVec.ofNat 64 (0x80800+8*(2*n+1))
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    rw [eq]
    exact outside ⟨1,by decide⟩
  rw [copy_mem]
  simp only [if_neg n1, if_neg n2]
  split_ifs with same
  · exact False.elim (n0 same)
  · rfl

theorem regular_step_other (hash : Hash) (s final : MachineState) (n : Nat)
    (pc : s.pc = 0x11d8) (small : n < 65)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (index : s.getReg .x19 = BitVec.ofNat 64 n)
    (trace : Trace hash image s 86 107 3 3 final) :
    OtherSlotFrame n s final := by
  have not65 : s.getReg .x19 ≠ 65#64 := by
    rw [index]
    exact word_ne_of_lt n 65 small (by decide)
  have not66 : s.getReg .x19 ≠ 66#64 := by
    rw [index]
    exact word_ne_of_lt n 66 (by omega) (by decide)
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.regular_from_entry hash s pc not65 not66
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = BitVec.ofNat 64 n :=
    readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready n (by omega) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 86 107 3 3 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  intro a lower upper outside
  rw [copy_other ready n (by omega) readyWord a lower upper outside]
  exact regular_from_entry_mid hash s ready pc not65 not66 first a lower upper

theorem special65_step_other (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 65#64)
    (index : s.getReg .x19 = 65#64)
    (trace : Trace hash image s 105 161 8 8 final) :
    OtherSlotFrame 65 s final := by
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special65_from_entry hash s pc index
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = 65#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 65 (by decide) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 105 161 8 8 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  intro a lower upper outside
  rw [copy_other ready 65 (by decide) readyWord a lower upper outside]
  exact special65_from_entry_mid hash s ready pc index first a lower upper

theorem special66_step_other (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x11d8)
    (counter : s.getMem 0x81030 = 66#64)
    (index : s.getReg .x19 = 66#64)
    (trace : Trace hash image s 114 184 10 10 final) :
    OtherSlotFrame 66 s final := by
  obtain ⟨ready, first, rest⟩ :=
    GroupedBalancedKeygenWotsChainRun67.special66_from_entry hash s pc index
  have readyPC : ready.pc = 0x12d0 := rest.1
  have readyCounter : ready.getMem 0x81030 = s.getMem 0x81030 := rest.2.2.1
  have readyWord : ready.getMem 0x81030 = 66#64 := readyCounter.trans counter
  obtain ⟨safe,safeNext⟩ := address_safe ready 66 (by decide) readyWord
  let made := copyState ready
  have second : Trace hash image ready 19 19 0 0 made :=
    (copy_steps ready readyPC safe safeNext).trace (hash := hash)
  have full : Trace hash image s 114 184 10 10 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  intro a lower upper outside
  rw [copy_other ready 66 (by decide) readyWord a lower upper outside]
  exact special66_from_entry_mid hash s ready pc index first a lower upper

#print axioms copy_other
#print axioms regular_step_other
#print axioms special65_step_other
#print axioms special66_step_other

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalMidCopy67

end

/-! The actual H1 seed and H2 chain produce a reference WOTS endpoint. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalStep67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem regular_even_endpoint (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf k : Nat) (bound : k < 33)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 213 241 4 4 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*(2*k)+i.val)) =
          (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
            ⟨2*k,by omega⟩).extractLsb' (64*i.val) 64) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,readyLevel,
    readyLeaf,readySeed,readyHigh,readyControl,readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf k (by omega) pc counter level address secret
  have readyAddress : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [Signing.wordAddress] using readyLeaf.trans (address ⟨0,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨0,by decide⟩).trans (address ⟨1,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨1,by decide⟩).trans (address ⟨2,by decide⟩)
  have seed : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
          ⟨2*k,by omega⟩).extractLsb' (64*i.val) 64 := by
    intro i
    exact (readySeed i).trans
      (GroupedBalancedKeygenLeafFunctionalSeed67.even_secret_words
        hash secretKey leaf k (by omega) i)
  obtain ⟨final,second,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalChain67.regular_step_endpoint
      hash ready 156 leaf (2*k)
      (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
        ⟨2*k,by omega⟩) readyPC (by omega) (by decide)
      readyCounter readyLevel readyIndex readyAddress seed
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · intro i
    have result := words i
    simpa only [GroupedBalancedUpperTree67.endpoint,
      GroupedBalancedChecksum67.maxDigit,
      if_pos (show 2*k < 65 by omega)] using result

theorem regular_odd_endpoint (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf n : Nat) (bound : n < 65)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (level : s.getMem 0x81000 = 156)
    (parity : n%2 = 1)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
          (128+64*i.val) 64) :
    ∃ final,
      Trace hash image s 112 133 3 3 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*n+i.val)) =
          (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
            ⟨n,by omega⟩).extractLsb' (64*i.val) 64) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,readyLevel,
    readyLeaf,readySeed,readyHigh,readyControl,readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf n pc (by omega) counter odd cached
  have readyAddress : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [Signing.wordAddress] using readyLeaf.trans (address ⟨0,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨0,by decide⟩).trans (address ⟨1,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨1,by decide⟩).trans (address ⟨2,by decide⟩)
  have seed : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
          ⟨n,by omega⟩).extractLsb' (64*i.val) 64 := by
    intro i
    exact (readySeed i).trans
      (GroupedBalancedKeygenLeafFunctionalSeed67.odd_secret_words
        hash secretKey leaf n (by omega) parity i)
  obtain ⟨final,second,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalChain67.regular_step_endpoint
      hash ready 156 leaf n
      (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
        ⟨n,by omega⟩) readyPC bound (by decide)
      readyCounter (readyLevel.trans level) readyIndex readyAddress seed
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · intro i
    have result := words i
    simpa only [GroupedBalancedUpperTree67.endpoint,
      GroupedBalancedChecksum67.maxDigit,
      if_pos bound] using result

theorem special65_endpoint (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 65#64)
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf 32).extractLsb'
          (128+64*i.val) 64) :
    ∃ final,
      Trace hash image s 131 187 8 8 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*65+i.val)) =
          (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
            ⟨65,by decide⟩).extractLsb' (64*i.val) 64) := by
  have odd : s.getMem 0x81030 &&& 1 ≠ 0 := by rw [counter]; decide
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,readyLevel,
    readyLeaf,readySeed,readyHigh,readyControl,readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf 65 pc (by decide) counter odd
      (by simpa using cached)
  have readyAddress : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [Signing.wordAddress] using readyLeaf.trans (address ⟨0,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨0,by decide⟩).trans (address ⟨1,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨1,by decide⟩).trans (address ⟨2,by decide⟩)
  have seed : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
          ⟨65,by decide⟩).extractLsb' (64*i.val) 64 := by
    intro i
    exact (readySeed i).trans
      (GroupedBalancedKeygenLeafFunctionalSeed67.odd_secret_words
        hash secretKey leaf 65 (by decide) (by decide) i)
  obtain ⟨final,second,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalChain67.special65_step_endpoint
      hash ready 156 leaf
      (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
        ⟨65,by decide⟩) readyPC (by decide)
      readyCounter (readyLevel.trans level) readyIndex readyAddress seed
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · intro i
    have result := words i
    simpa [GroupedBalancedUpperTree67.endpoint,
      GroupedBalancedChecksum67.maxDigit] using result

theorem special66_endpoint (hash : Hash) (secretKey : SecretKey)
    (s : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 66#64)
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 241 318 11 11 final ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80800 (2*66+i.val)) =
          (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
            ⟨66,by decide⟩).extractLsb' (64*i.val) 64) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,readyLevel,
    readyLeaf,readySeed,readyHigh,readyControl,readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf 33 (by decide) pc counter level address secret
  have readyAddress : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [Signing.wordAddress] using readyLeaf.trans (address ⟨0,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨0,by decide⟩).trans (address ⟨1,by decide⟩)
    · simpa [Signing.wordAddress] using
        (readyControl ⟨1,by decide⟩).trans (address ⟨2,by decide⟩)
  have seed : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
          ⟨66,by decide⟩).extractLsb' (64*i.val) 64 := by
    intro i
    exact (readySeed i).trans
      (GroupedBalancedKeygenLeafFunctionalSeed67.even_secret_words
        hash secretKey leaf 33 (by decide) i)
  obtain ⟨final,second,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalChain67.special66_step_endpoint
      hash ready 156 leaf
      (GroupedBalancedUpperTree67.secret hash secretKey 156 leaf
        ⟨66,by decide⟩) readyPC (by decide)
      readyCounter readyLevel readyIndex readyAddress seed
  refine ⟨final,?_,?_⟩
  · simpa only [Nat.reduceAdd] using first.trans second
  · intro i
    have result := words i
    simpa [GroupedBalancedUpperTree67.endpoint,
      GroupedBalancedChecksum67.maxDigit] using result

#print axioms regular_even_endpoint
#print axioms regular_odd_endpoint
#print axioms special65_endpoint
#print axioms special66_endpoint

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalStep67
