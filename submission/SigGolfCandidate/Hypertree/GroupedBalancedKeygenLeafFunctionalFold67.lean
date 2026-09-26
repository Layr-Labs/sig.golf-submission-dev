import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalStep67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenCacheChainStep67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFullChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEvenChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOddChain67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSuffix67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFrame67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFold67. -/
section
/-! Endpoint-table, cached seed, and loaded secret-key frames across full chains. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalMidCopy67
open GroupedBalancedKeygenCacheTick67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def PriorTableFrame (n : Nat) (before after : MachineState) : Prop :=
  ∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
    (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80800 (2*n+i.val)) →
    after.getMem a = before.getMem a

theorem prior_table_trans {s ready final : MachineState} (n : Nat)
    (first : ∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
      ready.getMem a = s.getMem a)
    (second : OtherSlotFrame n ready final) :
    PriorTableFrame n s final := by
  intro a lower upper outside
  rw [second a lower (by omega) outside, first a lower upper]

theorem high_cache_outside (s : MachineState) (n : Nat) (bound : n < 67)
    (i : Fin 2) :
    (∀ j : Fin 2, Signing.wordAddress 0x80d10 i.val ≠
      Signing.wordAddress 0x80800 (2*n+j.val)) := by
  intro j same
  have h := congrArg BitVec.toNat same
  fin_cases i <;> fin_cases j <;>
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0x80800+8*(2*n+0) < 2^64),
      Nat.mod_eq_of_lt (by omega : 0x80800+8*(2*n+1) < 2^64)] at h <;>
    omega

theorem regular_even_frame (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf k : Nat) (bound : k < 33)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s 213 241 4 4 final) :
    PriorTableFrame (2*k) s final ∧
    (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) ∧
    (∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf k).extractLsb'
          (128+64*i.val) 64) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,_,_,_,
    readyHigh,_,readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf k (by omega) pc counter level address secret
  obtain ⟨made,second,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready (2*k)
      readyPC (by omega) readyCounter readyIndex
  have full : Trace hash image s 213 241 4 4 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  have mid := GroupedBalancedKeygenLeafFunctionalMidCopy67.regular_step_other
    hash ready made (2*k) readyPC (by omega) readyCounter readyIndex second
  have low := GroupedBalancedKeygenCacheChainStep67.regular_step_low
    hash ready made (2*k) readyPC (by omega) readyCounter readyIndex second
  refine ⟨prior_table_trans (2*k) readyTable mid,?_,?_⟩
  · intro a small
    rw [low a (by omega),readySource a small]
  · intro i
    rw [mid _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (high_cache_outside ready (2*k) (by omega) i),readyHigh i]

theorem regular_odd_frame (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf n : Nat) (bound : n < 65)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
          (128+64*i.val) 64)
    (trace : Trace hash image s 112 133 3 3 final) :
    PriorTableFrame n s final ∧
    (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,_,_,_,_,_,
    readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf n pc (by omega) counter odd cached
  obtain ⟨made,second,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.regular_step hash ready n
      readyPC bound readyCounter readyIndex
  have full : Trace hash image s 112 133 3 3 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  have mid := GroupedBalancedKeygenLeafFunctionalMidCopy67.regular_step_other
    hash ready made n readyPC bound readyCounter readyIndex second
  have low := GroupedBalancedKeygenCacheChainStep67.regular_step_low
    hash ready made n readyPC bound readyCounter readyIndex second
  refine ⟨prior_table_trans n readyTable mid,?_⟩
  intro a small
  rw [low a (by omega),readySource a small]

theorem special65_frame (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 65#64)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf 32).extractLsb'
          (128+64*i.val) 64)
    (trace : Trace hash image s 131 187 8 8 final) :
    PriorTableFrame 65 s final ∧
    (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,_,_,_,_,_,
    readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf 65 pc (by decide) counter odd (by simpa using cached)
  obtain ⟨made,second,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special65_step hash ready
      readyPC readyCounter readyIndex
  have full : Trace hash image s 131 187 8 8 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  have mid := GroupedBalancedKeygenLeafFunctionalMidCopy67.special65_step_other
    hash ready made readyPC readyCounter readyIndex second
  have low := GroupedBalancedKeygenCacheChainStep67.special65_step_low
    hash ready made readyPC readyCounter readyIndex second
  refine ⟨prior_table_trans 65 readyTable mid,?_⟩
  intro a small
  rw [low a (by omega),readySource a small]

theorem special66_frame (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 66#64)
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s 241 318 11 11 final) :
    PriorTableFrame 66 s final ∧
    (∀ a : Word, a.toNat < 0x100 → final.getMem a = s.getMem a) := by
  obtain ⟨ready,first,readyPC,readyIndex,readyCounter,_,_,_,_,_,
    readyTable,readySource⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf 33 (by decide) pc (by simpa using counter)
        level address secret
  obtain ⟨made,second,_,_,_,_,_⟩ :=
    GroupedBalancedKeygenChainStep67.special66_step hash ready
      readyPC (by simpa using readyCounter) (by simpa using readyIndex)
  have full : Trace hash image s 241 318 11 11 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace full
  rw [same]
  have mid := GroupedBalancedKeygenLeafFunctionalMidCopy67.special66_step_other
    hash ready made readyPC (by simpa using readyCounter)
      (by simpa using readyIndex) second
  have low := GroupedBalancedKeygenCacheChainStep67.special66_step_low
    hash ready made readyPC (by simpa using readyCounter)
      (by simpa using readyIndex) second
  refine ⟨prior_table_trans 66 readyTable mid,?_⟩
  intro a small
  rw [low a (by omega),readySource a small]

#print axioms regular_even_frame
#print axioms regular_odd_frame
#print axioms special65_frame
#print axioms special66_frame

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFrame67

end

/-! The endpoint-table invariant for the 67-chain direct keygen loop. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalFrame67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def Prefix (hash : Hash) (secretKey : SecretKey) (leaf n : Nat)
    (s : MachineState) : Prop :=
  ∀ m : Fin 67, m.val < n → ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x80800 (2*m.val+i.val)) =
      (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf m).extractLsb'
        (64*i.val) 64

theorem Prefix.zero (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState) : Prefix hash secretKey leaf 0 s := by
  intro m hm
  omega

private theorem address_range (n : Nat) (bound : n < 67) (i : Fin 2) :
    0x80800 ≤ (Signing.wordAddress 0x80800 (2*n+i.val)).toNat ∧
    (Signing.wordAddress 0x80800 (2*n+i.val)).toNat < 0x80d00 := by
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have := i.isLt
  omega

private theorem other_slot (m : Fin 67) (n : Nat)
    (small : m.val < n) (bound : n < 67) (i j : Fin 2) :
    Signing.wordAddress 0x80800 (2*m.val+i.val) ≠
      Signing.wordAddress 0x80800 (2*n+j.val) := by
  intro same
  have h := congrArg BitVec.toNat same
  simp only [Signing.wordAddress,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := i.isLt; have := j.isLt; omega)] at h
  have := i.isLt
  have := j.isLt
  omega

theorem Prefix.step (hash : Hash) (secretKey : SecretKey)
    (leaf n : Nat) (bound : n < 67) (s final : MachineState)
    (prior : Prefix hash secretKey leaf n s)
    (frame : PriorTableFrame n s final)
    (fresh : ∀ i : Fin 2,
      final.getMem (Signing.wordAddress 0x80800 (2*n+i.val)) =
        (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
          ⟨n,bound⟩).extractLsb' (64*i.val) 64) :
    Prefix hash secretKey leaf (n+1) final := by
  intro m hm i
  by_cases old : m.val < n
  · have range := address_range m.val m.isLt i
    rw [frame _ range.1 range.2
      (fun j => other_slot m n old bound i j)]
    exact prior m old i
  · have eqm : m.val = n := by omega
    have same : m = ⟨n,bound⟩ := Fin.eq_of_val_eq eqm
    subst m
    exact fresh i

structure EvenState (hash : Hash) (secretKey : SecretKey)
    (leaf k : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1050
  counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k)
  level : s.getMem 0x81000 = 156
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  secret : ∀ i : Fin 4,
    s.getMem (Signing.wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64
  prior : Prefix hash secretKey leaf (2*k) s

private theorem address_after (s t : MachineState) (leaf : Nat)
    (before : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (first : t.getMem 0x81008 = s.getMem 0x81008)
    (higher : GroupedBalancedKeygenRootControlsTick67.ControlFrame s t) :
    ∀ i : Fin 3,
      t.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
  intro i
  fin_cases i
  · simpa [Signing.wordAddress] using first.trans (before ⟨0,by decide⟩)
  · simpa [Signing.wordAddress] using higher.1.trans (before ⟨1,by decide⟩)
  · simpa [Signing.wordAddress] using higher.2.trans (before ⟨2,by decide⟩)

private theorem secret_after (s t : MachineState) (secretKey : SecretKey)
    (before : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (frame : ∀ a : Word, a.toNat < 0x100 → t.getMem a = s.getMem a) :
    ∀ i : Fin 4,
      t.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
  intro i
  rw [frame _ (by fin_cases i <;> decide)]
  exact before i

private theorem even_word (k : Nat) (bound : k < 33) :
    ((BitVec.ofNat 64 (2*k) : Word) &&& 1) = 0 := by
  interval_cases k <;> decide

private theorem odd_word (k : Nat) (bound : k < 32) :
    ((BitVec.ofNat 64 (2*k+1) : Word) &&& 1) ≠ 0 := by
  interval_cases k <;> decide

theorem regular_pair (hash : Hash) (secretKey : SecretKey)
    (leaf k : Nat) (bound : k < 32) (s : MachineState)
    (inv : EvenState hash secretKey leaf k s) :
    ∃ final,
      Trace hash image s 325 374 7 7 final ∧
      EvenState hash secretKey leaf (k+1) final := by
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [inv.counter]
    exact even_word k (by omega)
  obtain ⟨middle,first,firstWords⟩ :=
    GroupedBalancedKeygenLeafFunctionalStep67.regular_even_endpoint
      hash secretKey s leaf k (by omega) inv.pc inv.counter inv.level
      inv.address inv.secret
  obtain ⟨oldMiddle,oldFirst,oldPC,oldCounter,oldLevel,oldLeaf⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain
      hash s (2*k) inv.pc (by omega) inv.counter even inv.level
  have sameMiddle : middle = oldMiddle := Trace.deterministic first oldFirst
  have middlePC : middle.pc = 0x1050 := by rw [sameMiddle]; exact oldPC
  have middleCounter : middle.getMem 0x81030 = BitVec.ofNat 64 (2*k+1) := by
    rw [sameMiddle]
    simpa only [Nat.add_assoc] using oldCounter
  have middleLevel : middle.getMem 0x81000 = 156 := by
    rw [sameMiddle]
    exact oldLevel
  have middleLeaf : middle.getMem 0x81008 = s.getMem 0x81008 := by
    rw [sameMiddle]
    exact oldLeaf
  have middleControl :=
    GroupedBalancedKeygenRootControlsFullChain67.regular_even_control
      hash s middle (2*k) inv.pc (by omega) inv.counter even inv.level first
  have middleAddress := address_after s middle leaf inv.address
    middleLeaf middleControl.1
  obtain ⟨middleFrame,middleSource,middleHigh⟩ :=
    GroupedBalancedKeygenLeafFunctionalFrame67.regular_even_frame
      hash secretKey s middle leaf k (by omega) inv.pc inv.counter
      inv.level inv.address inv.secret first
  have middleSecret := secret_after s middle secretKey inv.secret middleSource
  have middlePrefix : Prefix hash secretKey leaf (2*k+1) middle :=
    Prefix.step hash secretKey leaf (2*k) (by omega) s middle
      inv.prior middleFrame firstWords
  have middleOdd : middle.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [middleCounter]
    exact odd_word k bound
  have middleCached : ∀ i : Fin 2,
      middle.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf
          ((2*k+1)/2)).extractLsb' (128+64*i.val) 64 := by
    intro i
    simpa [show (2*k+1)/2 = k by omega] using middleHigh i
  obtain ⟨final,second,secondWords⟩ :=
    GroupedBalancedKeygenLeafFunctionalStep67.regular_odd_endpoint
      hash secretKey middle leaf (2*k+1) (by omega)
      middlePC middleCounter middleLevel (by omega) middleOdd
      middleAddress middleCached
  obtain ⟨oldFinal,oldSecond,oldFinalPC,oldFinalCounter,oldFinalLevel,
    oldFinalLeaf⟩ :=
    GroupedBalancedKeygenOddChain67.regular_odd_chain
      hash middle (2*k+1) middlePC (by omega) middleCounter middleOdd
  have sameFinal : final = oldFinal := Trace.deterministic second oldSecond
  have finalPC : final.pc = 0x1050 := by rw [sameFinal]; exact oldFinalPC
  have finalCounter : final.getMem 0x81030 =
      BitVec.ofNat 64 (2*(k+1)) := by
    rw [sameFinal]
    simpa [show 2*(k+1)=2*k+2 by omega] using oldFinalCounter
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [sameFinal,oldFinalLevel]
    exact middleLevel
  have finalLeaf : final.getMem 0x81008 = middle.getMem 0x81008 := by
    rw [sameFinal]
    exact oldFinalLeaf
  have finalControl :=
    GroupedBalancedKeygenRootControlsFullChain67.regular_odd_control
      hash middle final (2*k+1) middlePC (by omega) middleCounter
      middleOdd second
  have finalAddress := address_after middle final leaf middleAddress
    finalLeaf finalControl.1
  obtain ⟨finalFrame,finalSource⟩ :=
    GroupedBalancedKeygenLeafFunctionalFrame67.regular_odd_frame
      hash secretKey middle final leaf (2*k+1) (by omega)
      middlePC middleCounter middleOdd middleCached second
  have finalSecret := secret_after middle final secretKey middleSecret finalSource
  have finalPrefix : Prefix hash secretKey leaf (2*(k+1)) final := by
    simpa [show 2*(k+1) = (2*k+1)+1 by omega] using
      Prefix.step hash secretKey leaf (2*k+1) (by omega) middle final
        middlePrefix finalFrame secondWords
  refine ⟨final,?_,⟨finalPC,finalCounter,finalLevel,finalAddress,
    finalSecret,finalPrefix⟩⟩
  simpa only [Nat.reduceAdd] using first.trans second

theorem regular_pairs (hash : Hash) (secretKey : SecretKey)
    (leaf k : Nat) (bound : k ≤ 32) (s : MachineState)
    (inv : EvenState hash secretKey leaf 0 s) :
    ∃ final,
      Trace hash image s (325*k) (374*k) (7*k) (7*k) final ∧
      EvenState hash secretKey leaf k final := by
  induction k with
  | zero =>
      exact ⟨s,by simpa using (Trace.refl s : Trace hash image s 0 0 0 0 s),inv⟩
  | succ k ih =>
      obtain ⟨middle,first,middleInv⟩ := ih (by omega)
      obtain ⟨final,second,finalInv⟩ :=
        regular_pair hash secretKey leaf k (by omega) middle middleInv
      refine ⟨final,?_,finalInv⟩
      simpa only [Nat.mul_succ,Nat.add_comm] using first.trans second

structure Odd65State (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1050
  counter : s.getMem 0x81030 = 65#64
  level : s.getMem 0x81000 = 156
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  secret : ∀ i : Fin 4,
    s.getMem (Signing.wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64
  prior : Prefix hash secretKey leaf 65 s
  cached : ∀ i : Fin 2,
    s.getMem (Signing.wordAddress 0x80d10 i.val) =
      (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf 32).extractLsb'
        (128+64*i.val) 64

theorem even64 (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState)
    (inv : EvenState hash secretKey leaf 32 s) :
    ∃ final,
      Trace hash image s 213 241 4 4 final ∧
      Odd65State hash secretKey leaf final := by
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [inv.counter]
    decide
  obtain ⟨final,trace,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalStep67.regular_even_endpoint
      hash secretKey s leaf 32 (by decide) inv.pc inv.counter inv.level
      inv.address inv.secret
  obtain ⟨old,oldTrace,oldPC,oldCounter,oldLevel,oldLeaf⟩ :=
    GroupedBalancedKeygenEvenChain67.regular_even_chain
      hash s 64 inv.pc (by decide) inv.counter even inv.level
  have same : final = old := Trace.deterministic trace oldTrace
  have finalPC : final.pc = 0x1050 := by rw [same]; exact oldPC
  have finalCounter : final.getMem 0x81030 = 65#64 := by
    rw [same]
    simpa using oldCounter
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [same]
    exact oldLevel
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [same]
    exact oldLeaf
  have control :=
    GroupedBalancedKeygenRootControlsFullChain67.regular_even_control
      hash s final 64 inv.pc (by decide) inv.counter even inv.level trace
  have finalAddress := address_after s final leaf inv.address finalLeaf control.1
  obtain ⟨table,source,high⟩ :=
    GroupedBalancedKeygenLeafFunctionalFrame67.regular_even_frame
      hash secretKey s final leaf 32 (by decide) inv.pc inv.counter
      inv.level inv.address inv.secret trace
  have finalSecret := secret_after s final secretKey inv.secret source
  have finalPrefix : Prefix hash secretKey leaf 65 final := by
    simpa using Prefix.step hash secretKey leaf 64 (by decide) s final
      inv.prior table words
  exact ⟨final,trace,⟨finalPC,finalCounter,finalLevel,finalAddress,
    finalSecret,finalPrefix,high⟩⟩

theorem odd65 (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState)
    (inv : Odd65State hash secretKey leaf s) :
    ∃ final,
      Trace hash image s 131 187 8 8 final ∧
      EvenState hash secretKey leaf 33 final := by
  have odd : s.getMem 0x81030 &&& 1 ≠ 0 := by
    rw [inv.counter]
    decide
  obtain ⟨final,trace,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalStep67.special65_endpoint
      hash secretKey s leaf inv.pc inv.counter inv.level inv.address inv.cached
  obtain ⟨old,oldTrace,oldPC,oldCounter,oldLevel,oldLeaf⟩ :=
    GroupedBalancedKeygenOddChain67.special65_odd_chain
      hash s inv.pc inv.counter odd
  have same : final = old := Trace.deterministic trace oldTrace
  have finalPC : final.pc = 0x1050 := by rw [same]; exact oldPC
  have finalCounter : final.getMem 0x81030 =
      BitVec.ofNat 64 (2*33) := by
    rw [same]
    simpa using oldCounter
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [same,oldLevel]
    exact inv.level
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [same]
    exact oldLeaf
  have control :=
    GroupedBalancedKeygenRootControlsFullChain67.special65_control
      hash s final inv.pc inv.counter odd trace
  have finalAddress := address_after s final leaf inv.address finalLeaf control.1
  obtain ⟨table,source⟩ :=
    GroupedBalancedKeygenLeafFunctionalFrame67.special65_frame
      hash secretKey s final leaf inv.pc inv.counter odd inv.cached trace
  have finalSecret := secret_after s final secretKey inv.secret source
  have finalPrefix : Prefix hash secretKey leaf (2*33) final := by
    simpa using Prefix.step hash secretKey leaf 65 (by decide) s final
      inv.prior table words
  exact ⟨final,trace,⟨finalPC,finalCounter,finalLevel,finalAddress,
    finalSecret,finalPrefix⟩⟩

structure CompleteState (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x131c
  level : s.getMem 0x81000 = 156
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64
  secret : ∀ i : Fin 4,
    s.getMem (Signing.wordAddress 0x20 i.val) =
      secretKey.extractLsb' (64*i.val) 64
  full : Prefix hash secretKey leaf 67 s

theorem even66 (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState)
    (inv : EvenState hash secretKey leaf 33 s) :
    ∃ final,
      Trace hash image s 241 318 11 11 final ∧
      CompleteState hash secretKey leaf final := by
  have even : s.getMem 0x81030 &&& 1 = 0 := by
    rw [inv.counter]
    decide
  obtain ⟨final,trace,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalStep67.special66_endpoint
      hash secretKey s leaf inv.pc (by simpa using inv.counter)
      inv.level inv.address inv.secret
  obtain ⟨old,oldTrace,oldPC,oldCounter,oldLevel,oldLeaf⟩ :=
    GroupedBalancedKeygenEvenChain67.special66_even_chain
      hash s inv.pc (by simpa using inv.counter) even inv.level
  have same : final = old := Trace.deterministic trace oldTrace
  have finalPC : final.pc = 0x131c := by rw [same]; exact oldPC
  have finalLevel : final.getMem 0x81000 = 156 := by
    rw [same]
    exact oldLevel
  have finalLeaf : final.getMem 0x81008 = s.getMem 0x81008 := by
    rw [same]
    exact oldLeaf
  have control :=
    GroupedBalancedKeygenRootControlsFullChain67.special66_control
      hash s final inv.pc (by simpa using inv.counter) even inv.level trace
  have finalAddress := address_after s final leaf inv.address finalLeaf control.1
  obtain ⟨table,source⟩ :=
    GroupedBalancedKeygenLeafFunctionalFrame67.special66_frame
      hash secretKey s final leaf inv.pc (by simpa using inv.counter)
      inv.level inv.address inv.secret trace
  have finalSecret := secret_after s final secretKey inv.secret source
  have finalPrefix : Prefix hash secretKey leaf 67 final := by
    simpa using Prefix.step hash secretKey leaf 66 (by decide) s final
      inv.prior table words
  exact ⟨final,trace,⟨finalPC,finalLevel,finalAddress,
    finalSecret,finalPrefix⟩⟩

theorem all_chains (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState)
    (inv : EvenState hash secretKey leaf 0 s) :
    ∃ final,
      Trace hash image s 10985 12714 247 247 final ∧
      CompleteState hash secretKey leaf final := by
  obtain ⟨after64,first,inv64⟩ :=
    regular_pairs hash secretKey leaf 32 (by decide) s inv
  obtain ⟨after65,second,inv65⟩ :=
    even64 hash secretKey leaf after64 inv64
  obtain ⟨after66,third,inv66⟩ :=
    odd65 hash secretKey leaf after65 inv65
  obtain ⟨final,fourth,complete⟩ :=
    even66 hash secretKey leaf after66 inv66
  refine ⟨final,?_,complete⟩
  simpa only [Nat.reduceMul,Nat.reduceAdd] using
    ((first.trans second).trans third).trans fourth

theorem Prefix.words (hash : Hash) (secretKey : SecretKey)
    (leaf : Nat) (s : MachineState)
    (full : Prefix hash secretKey leaf 67 s) :
    ∀ i : Fin 134,
      s.getMem (Signing.wordAddress 0x80800 i.val) =
        (GroupedBalancedUpperTree67.endpoint hash secretKey 156 leaf
          ⟨i.val/2,by have := i.isLt; omega⟩).extractLsb'
            (64*(i.val%2)) 64 := by
  intro i
  let chain : Fin 67 := ⟨i.val/2,by have := i.isLt; omega⟩
  let half : Fin 2 := ⟨i.val%2,by omega⟩
  have h := full chain (by have := i.isLt; omega) half
  have index : 2*(i.val/2)+(i.val%2)=i.val := by omega
  simpa only [chain,half,Fin.val_mk,index] using h

theorem leaf_counter_word (s : MachineState) (n : Nat)
    (bound : n < 16)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 n).extractLsb' (64*i.val) 64) :
    s.getMem 0x81008#64 = BitVec.ofNat 64 n := by
  have h := address ⟨0,by decide⟩
  have modn : n % 2^192 = n := Nat.mod_eq_of_lt (by omega)
  have hh : s.getMem 0x81008#64 = BitVec.ofNat 64 (n % 2^192) := by
    simpa [Signing.wordAddress,BitVec.extractLsb'] using h
  simpa only [modn] using hh

theorem leaf_from_entry (hash : Hash) (secretKey : SecretKey)
    (n : Nat) (bound : n < 16) (s : MachineState)
    (inv : EvenState hash secretKey n 0 s) :
    ∃ final,
      Trace hash image s 11850 13722 248 265 final ∧
      final.pc = (if n = 15 then 0x1428 else 0x1040) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x82000 (2*n+i.val)) =
          (GroupedBalancedUpperTree67.leafRoot hash secretKey 156 n).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨ready,first,complete⟩ := all_chains hash secretKey n s inv
  have counter := leaf_counter_word ready n bound complete.address
  obtain ⟨final,second,finalPC,words⟩ :=
    GroupedBalancedKeygenLeafFunctionalSuffix67.leaf_suffix_root
      hash secretKey ready 156 n complete.pc bound complete.level counter
      complete.address (Prefix.words hash secretKey n ready complete.full)
  refine ⟨final,?_,finalPC,words⟩
  simpa only [Nat.reduceAdd] using first.trans second

theorem entry_even (hash : Hash) (secretKey : SecretKey)
    (s : MachineState)
    (source : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (pc : s.pc = 0x1000) :
    EvenState hash secretKey 0 0
      (GroupedBalancedKeygenPrefix67.entryState s) := by
  let t := GroupedBalancedKeygenPrefix67.entryState s
  obtain ⟨level,address0,address1,address2,counter⟩ :=
    GroupedBalancedKeygenPrefix67.entry_words s
  refine ⟨GroupedBalancedKeygenPrefix67.entry_pc s pc,
    by simpa using counter,level,?_,?_,Prefix.zero hash secretKey 0 t⟩
  · intro i
    fin_cases i
    · simpa [Signing.wordAddress,BitVec.extractLsb'] using address0
    · simpa [Signing.wordAddress,BitVec.extractLsb'] using address1
    · simpa [Signing.wordAddress,BitVec.extractLsb'] using address2
  · intro i
    rw [GroupedBalancedKeygenPrefix67.entry_mem_other s _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact source i

#print axioms Prefix.step
#print axioms regular_pair
#print axioms regular_pairs
#print axioms even64
#print axioms odd65
#print axioms even66
#print axioms all_chains
#print axioms Prefix.words
#print axioms leaf_counter_word
#print axioms leaf_from_entry
#print axioms entry_even

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFold67
