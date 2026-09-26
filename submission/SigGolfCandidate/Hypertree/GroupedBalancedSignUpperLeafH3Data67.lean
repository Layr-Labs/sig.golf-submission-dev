import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddressStep67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Complete67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomStackSlots67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLeafInvariant67


/-! Address arithmetic for an eight- or sixteen-leaf upper tree. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafArithmetic67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

theorem within_group_no_carry (base i height : Nat)
    (hh : height = 3 ∨ height = 4)
    (aligned : base % 2^height = 0)
    (next : i+1 < 2^height) :
    (base+i) % 1024 < 1023 := by
  rcases hh with rfl | rfl
  · norm_num at aligned next ⊢
    have hmod : (base % 1024) % 8 = 0 := by omega
    have hbase : base % 1024 ≤ 1016 := by omega
    omega
  · norm_num at aligned next ⊢
    have hmod : (base % 1024) % 16 = 0 := by omega
    have hbase : base % 1024 ≤ 1008 := by omega
    omega

theorem next_words (base i height : Nat)
    (hh : height = 3 ∨ height = 4)
    (aligned : base % 2^height = 0)
    (bound : base+2^height ≤ 2^160)
    (next : i+1 < 2^height) :
    (BitVec.ofNat 192 (base+i+1)).extractLsb' 0 64 =
      (BitVec.ofNat 192 (base+i)).extractLsb' 0 64 + 1 ∧
    (BitVec.ofNat 192 (base+i+1)).extractLsb' 64 64 =
      (BitVec.ofNat 192 (base+i)).extractLsb' 64 64 ∧
    (BitVec.ofNat 192 (base+i+1)).extractLsb' 128 64 =
      (BitVec.ofNat 192 (base+i)).extractLsb' 128 64 := by
  have hleaf : base+i < 2^160 := by omega
  have hmod := within_group_no_carry base i height hh aligned next
  exact ⟨GroupedBalancedSignBottomAddressStep67.low_step (base+i) hleaf hmod,
    GroupedBalancedSignBottomAddressStep67.middle_step (base+i) hleaf hmod,
    GroupedBalancedSignBottomAddressStep67.high_step (base+i) hleaf hmod⟩

#print axioms within_group_no_carry
#print axioms next_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafArithmetic67


/-! The H3 call stores one completed upper WOTS leaf and advances the leaf cursor. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafH3Data67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomStackSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

structure Ready (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected i : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1b28
  count : s.getMem 0x810e0 = BitVec.ofNat 64 i
  limit : s.getMem 0x810d0 = BitVec.ofNat 64 (2^height)
  chosen : s.getMem 0x810e8 = BitVec.ofNat 64 selected
  tree : s.getMem 0x81000 = BitVec.ofNat 64 treeBase
  address : ∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 w.val) =
      (BitVec.ofNat 192 (leafBase+i)).extractLsb' (64*w.val) 64
  scratch : ∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 w.val) =
      (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64
  previous : ∀ j : Nat, j < i → ∀ w : Fin 2,
    s.getMem (slot j w.val) =
      (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (leafBase+j)).extractLsb' (64*w.val) 64
  endpoints : ∀ j : Fin 134,
    s.getMem (Signing.wordAddress 0x80020 j.val) =
      (GroupedBalancedUpperTree67.endpoint hash secretKey treeBase
        (leafBase+i) ⟨j.val/2,by have := j.isLt; omega⟩).extractLsb'
          (64*(j.val%2)) 64

structure After (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected i : Nat) (s : MachineState) : Prop where
  pc : s.pc = (if i<2^height then 0x1750 else 0x1c30)
  count : s.getMem 0x810e0 = BitVec.ofNat 64 i
  limit : s.getMem 0x810d0 = BitVec.ofNat 64 (2^height)
  chosen : s.getMem 0x810e8 = BitVec.ofNat 64 selected
  tree : s.getMem 0x81000 = BitVec.ofNat 64 treeBase
  address : ∀ (hi : i<2^height) (w : Fin 3),
    s.getMem (Signing.wordAddress 0x81008 w.val) =
      (BitVec.ofNat 192 (leafBase+i)).extractLsb' (64*w.val) 64
  scratch : ∀ w : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 w.val) =
      (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64
  previous : ∀ j : Nat, j < i → ∀ w : Fin 2,
    s.getMem (slot j w.val) =
      (GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (leafBase+j)).extractLsb' (64*w.val) 64

theorem word_succ (i : Nat) (hi : i < 16) :
    BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i+1) := by
  simpa using GroupedBalancedSignBottomLeafInvariant67.word_succ i (by omega)

theorem word_limit (i height : Nat) (hi : i < 2^height)
    (hh : height = 3 ∨ height = 4) :
    (BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (2^height)) ↔
      i+1=2^height := by
  rw [word_succ i (by rcases hh with rfl | rfl <;> omega)]
  constructor
  · intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at hn
    have hl : i+1 < 2^64 := by rcases hh with rfl | rfl <;> omega
    have hh' : 2^height < 2^64 := by rcases hh with rfl | rfl <;> omega
    rw [Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hh'] at hn
    exact hn
  · intro eq
    rw [eq]

theorem leaf_hash (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase i : Nat) :
    GroupedBalancedUpperTree67.compressLeaf hash treeBase (leafBase+i)
      (GroupedBalancedUpperTree67.endpoint hash secretKey treeBase
        (leafBase+i)) =
      GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (leafBase+i) := rfl

theorem one_leaf (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected i : Nat) (s : MachineState)
    (hh : height = 3 ∨ height = 4)
    (aligned : leafBase % 2^height = 0)
    (bound : leafBase+2^height ≤ 2^160)
    (hi : i < 2^height)
    (ready : Ready hash secretKey treeBase leafBase height selected i s) :
    ∃ next : MachineState,
      Trace hash image s 66 209 1 18 next ∧
      After hash secretKey treeBase leafBase height selected (i+1) next ∧
      (∀ a : Word, 0x81000 ≤ a.toNat →
        a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) →
        a ≠ GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0)+8 →
        a ≠ 0x81008 → a ≠ 0x810e0 → next.getMem a = s.getMem a) ∧
      next.getReg .x2 = s.getReg .x2 ∧
      (∀ a : Word, a.toNat < 0x80000 → next.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        next.getMem a=s.getMem a) := by
  have hsmall : i < 16 := by rcases hh with rfl | rfl <;> omega
  have countBound : (s.getMem 0x810e0).toNat < 16 := by
    rw [ready.count]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i<2^64)]
    exact hsmall
  obtain ⟨next,trace,nextCount,nextLow,store0,store8,nextPc,frame,nextSp,lowFrame,digitFrame⟩ :=
    GroupedBalancedSignUpperH3Complete67.leaf_to_next hash s treeBase
      (leafBase+i)
      (GroupedBalancedUpperTree67.endpoint hash secretKey treeBase (leafBase+i))
      ready.pc countBound ready.tree ready.address ready.endpoints
  have belowFrame (a : Word) (high : 0x81000 ≤ a.toNat)
      (low : a.toNat < 0x83000) (not08 : a ≠ 0x81008)
      (notE0 : a ≠ 0x810e0) : next.getMem a = s.getMem a := by
    obtain ⟨ne0,ne8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (s.getMem 0x810e0) a (by omega : (s.getMem 0x810e0).toNat < 1024) low
    exact frame a high ne0 ne8 not08 notE0
  refine ⟨next,trace,?_,frame,nextSp,lowFrame,digitFrame⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [nextPc,ready.count,ready.limit]
    by_cases hnext : i+1 < 2^height
    · have notLast : i+1 ≠ 2^height := by omega
      have ne : ¬ (BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (2^height)) :=
        fun eq => notLast ((word_limit i height hi hh).mp eq)
      rcases hh with h3 | h4
      · have hn : i+1<8 := by simpa [h3] using hnext
        have hw : ¬ (BitVec.ofNat 64 i + 1 = (8 : Word)) := by
          simpa [h3] using ne
        simpa [h3,hn,hw]
      · have hn : i+1<16 := by simpa [h4] using hnext
        have hw : ¬ (BitVec.ofNat 64 i + 1 = (16 : Word)) := by
          simpa [h4] using ne
        simpa [h4,hn,hw]
    · have last : i+1=2^height := by omega
      have eq : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (2^height) :=
        (word_limit i height hi hh).mpr last
      rcases hh with h3 | h4
      · have hn : ¬ i+1<8 := by simpa [h3] using hnext
        have hw : BitVec.ofNat 64 i + 1 = (8 : Word) := by
          simpa [h3] using eq
        simpa [h3,hn,hw]
      · have hn : ¬ i+1<16 := by simpa [h4] using hnext
        have hw : BitVec.ofNat 64 i + 1 = (16 : Word) := by
          simpa [h4] using eq
        simpa [h4,hn,hw]
  · rw [nextCount,ready.count,word_succ i hsmall]
  · exact (belowFrame 0x810d0 (by decide) (by decide)
      (by decide) (by decide)).trans ready.limit
  · exact (belowFrame 0x810e8 (by decide) (by decide)
      (by decide) (by decide)).trans ready.chosen
  · exact (belowFrame 0x81000 (by decide) (by decide)
      (by decide) (by decide)).trans ready.tree
  · intro hnext w
    have word := GroupedBalancedSignUpperLeafArithmetic67.next_words
      leafBase i height hh aligned bound hnext
    fin_cases w
    · change next.getMem 0x81008 = _
      have old : s.getMem 0x81008 =
          (BitVec.ofNat 192 (leafBase+i)).extractLsb' 0 64 := by
        simpa [Signing.wordAddress] using ready.address (0 : Fin 3)
      rw [nextLow,old]
      simpa only [Nat.add_assoc] using word.1.symm
    · change next.getMem 0x81010 = _
      have old : s.getMem 0x81010 =
          (BitVec.ofNat 192 (leafBase+i)).extractLsb' 64 64 := by
        simpa [Signing.wordAddress] using ready.address (1 : Fin 3)
      rw [belowFrame 0x81010 (by decide) (by decide)
        (by decide) (by decide),old]
      simpa only [Nat.add_assoc] using word.2.1.symm
    · change next.getMem 0x81018 = _
      have old : s.getMem 0x81018 =
          (BitVec.ofNat 192 (leafBase+i)).extractLsb' 128 64 := by
        simpa [Signing.wordAddress] using ready.address (2 : Fin 3)
      rw [belowFrame 0x81018 (by decide) (by decide)
        (by decide) (by decide),old]
      simpa only [Nat.add_assoc] using word.2.2.symm
  · intro w
    rw [belowFrame _ (by fin_cases w <;> decide)
      (by fin_cases w <;> decide)
      (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
    exact ready.scratch w
  · intro j hj w
    by_cases current : j=i
    · subst j
      fin_cases w
      · rw [slot0_dynamic i (by omega),← ready.count]
        simpa only [leaf_hash] using store0
      · rw [slot1_dynamic i (by omega),← ready.count]
        simpa only [leaf_hash] using store8
    · have priorIndex : j < i := by omega
      have separate0 : slot j w.val ≠
          GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0) := by
        rw [ready.count,← slot0_dynamic i (by omega)]
        exact earlier_ne i j w.val 0 (by omega) priorIndex w.isLt (by decide)
      have separate8 : slot j w.val ≠
          GroupedBalancedSignBottomStackBound67.stack0 (s.getMem 0x810e0)+8 := by
        rw [ready.count,← slot1_dynamic i (by omega)]
        exact earlier_ne i j w.val 1 (by omega) priorIndex w.isLt (by decide)
      have range := slot_range j w.val (by omega) w.isLt
      have ne08 : slot j w.val ≠ 0x81008 :=
        slot_ne_below j w.val (by omega) w.isLt 0x81008 (by decide)
      have neE0 : slot j w.val ≠ 0x810e0 :=
        slot_ne_below j w.val (by omega) w.isLt 0x810e0 (by decide)
      have high : 0x81000 ≤ (slot j w.val).toNat := by omega
      exact (frame (slot j w.val) high separate0 separate8 ne08 neE0).trans
        (ready.previous j priorIndex w)

#print axioms one_leaf
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafH3Data67
