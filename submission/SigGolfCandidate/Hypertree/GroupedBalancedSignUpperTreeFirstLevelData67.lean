import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeCallee67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeModel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstControl67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstLevelData67. -/
section
/-! Functional table invariant for repeated upper Merkle parent hashes. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev tick := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

structure Params (leafBase height limit source target addressBase : Nat) : Prop where
  small : 0 < limit ∧ limit ≤ 8
  limitCase : limit=1 ∨ limit=2 ∨ limit=4 ∨ limit=8
  addressAligned : addressBase % limit = 0
  addressDef : addressBase=leafBase/2^(height+1)
  addressBound : addressBase+limit < 2^160
  bases : (source=0x83000 ∧ target=0x88000) ∨
    (source=0x88000 ∧ target=0x83000)

structure At (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase n : Nat) (s : MachineState) : Prop where
  pc : s.pc=0x1f08
  counter : s.getMem 0x810d8=BitVec.ofNat 64 n
  count : s.getMem 0x810d0=BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0=BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8=BitVec.ofNat 64 target
  heightWord : s.getMem 0x81000=BitVec.ofNat 64 (treeBase+height)
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val)=
      (BitVec.ofNat 192 (addressBase+n)).extractLsb' (64*i.val) 64
  sourceWords : ∀ j, j<2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val))=
      (node hash treeBase leafBase leaves height j).extractLsb' (64*i.val) 64
  targetWords : ∀ j, j<n → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
      (node hash treeBase leafBase leaves (height+1) j).extractLsb' (64*i.val) 64
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val)=
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64

structure Done (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase : Nat) (s : MachineState) : Prop where
  pc : s.pc=0x2058
  counter : s.getMem 0x810d8=BitVec.ofNat 64 limit
  count : s.getMem 0x810d0=BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0=BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8=BitVec.ofNat 64 target
  heightWord : s.getMem 0x81000=BitVec.ofNat 64 (treeBase+height)
  sourceWords : ∀ j, j<2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val))=
      (node hash treeBase leafBase leaves height j).extractLsb' (64*i.val) 64
  targetWords : ∀ j, j<limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
      (node hash treeBase leafBase leaves (height+1) j).extractLsb' (64*i.val) 64
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val)=
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64

theorem no_carry (addressBase limit n : Nat)
    (cases : limit=1 ∨ limit=2 ∨ limit=4 ∨ limit=8)
    (aligned : addressBase%limit=0) (next : n+1<limit) :
    (addressBase+n)%18446744073709551616+1<18446744073709551616 := by
  rcases cases with h|h|h|h <;> subst limit <;>
    norm_num at * <;> omega

theorem child_left (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase n : Nat) (s : MachineState)
    (holds : At hash treeBase leafBase leaves height limit source target
      addressBase n s)
    (nBound : n<limit) (i : Fin 2) :
    s.getMem
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 (8*i.val))=
      (node hash treeBase leafBase leaves height (2*n)).extractLsb'
        (64*i.val) 64 := by
  rw [GroupedBalancedSignBottomTreePointerData67.pair_reg_nat s n source
    holds.counter holds.sourcePtr]
  have h := holds.sourceWords (2*n) (by omega) i
  have hn : 16*(2*n)=32*n := by omega
  rw [hn] at h
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using h

theorem child_right (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase n : Nat) (s : MachineState)
    (holds : At hash treeBase leafBase leaves height limit source target
      addressBase n s)
    (nBound : n<limit) (i : Fin 2) :
    s.getMem
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 (16+8*i.val))=
      (node hash treeBase leafBase leaves height (2*n+1)).extractLsb'
        (64*i.val) 64 := by
  rw [GroupedBalancedSignBottomTreePointerData67.pair_reg_nat s n source
    holds.counter holds.sourcePtr]
  have h := holds.sourceWords (2*n+1) (by omega) i
  have hn : 16*(2*n+1)=32*n+16 := by omega
  rw [hn] at h
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using h

theorem one_tick (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (holds : At hash treeBase leafBase leaves height limit source target
      addressBase n s)
    (nBound : n<limit) :
    Trace hash image s 84 91 1 1 (tick hash s) ∧
    (n+1<limit → At hash treeBase leafBase leaves height limit source target
      addressBase (n+1) (tick hash s)) ∧
    (n+1=limit → Done hash treeBase leafBase leaves height limit source target
      addressBase (tick hash s)) := by
  have limitBound : limit ≤ 8 := params.small.2
  have addressBound : addressBase+limit < 2^160 := params.addressBound
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases params.bases with ⟨h,_⟩|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases params.bases with ⟨_,h⟩|⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have pAt : GroupedBalancedSignUpperTreeParentTrace67.At
      limit source target n s :=
    ⟨holds.pc,holds.counter,holds.count,holds.sourcePtr,holds.targetPtr⟩
  obtain ⟨trace,next,finish,frame,_,_⟩ :=
    GroupedBalancedSignUpperTreeParentTrace67.one_tick hash limit source target
      n s pAt params.small.2 nBound sourceCase targetCase
  have stable (a : Word) (hi : 0x81000 ≤ a.toNat)
      (lo : a.toNat < 0x83000) (ne08 : a ≠ 0x81008)
      (ned8 : a ≠ 0x810d8) :
      (tick hash s).getMem a=s.getMem a :=
    frame a ⟨hi,lo,ne08,ned8⟩
  have heightWord : (tick hash s).getMem 0x81000=
      BitVec.ofNat 64 (treeBase+height) := by
    rw [stable 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact holds.heightWord
  have sourceWords : ∀ j, j<2*limit → ∀ i : Fin 2,
      (tick hash s).getMem (BitVec.ofNat 64 (source+16*j+8*i.val))=
      (node hash treeBase leafBase leaves height j).extractLsb'
        (64*i.val) 64 := by
    intro j hj i
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_source_slots
      hash s n source target j i holds.counter holds.targetPtr
      (by omega) (by omega) params.bases]
    exact holds.sourceWords j hj i
  have output := GroupedBalancedSignBottomTreeInnerTickData67.output_node_at
    hash s n target (treeBase+height) (addressBase+n)
    (node hash treeBase leafBase leaves height (2*n))
    (node hash treeBase leafBase leaves height (2*n+1))
    holds.counter holds.targetPtr (by omega) targetCase
    holds.heightWord holds.address
    (child_left hash treeBase leafBase leaves height limit source target
      addressBase n s holds nBound)
    (child_right hash treeBase leafBase leaves height limit source target
      addressBase n s holds nBound)
  have hnew : ∀ i : Fin 2,
      (tick hash s).getMem (BitVec.ofNat 64 (target+16*n+8*i.val))=
        (node hash treeBase leafBase leaves (height+1) n).extractLsb'
          (64*i.val) 64 := by
    intro i
    have h := output i
    rw [params.addressDef] at h
    simpa only [node,GroupedBalancedSignUpperTreeModel67.parent] using h
  have targetWords : ∀ j, j<n+1 → ∀ i : Fin 2,
      (tick hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
        (node hash treeBase leafBase leaves (height+1) j).extractLsb'
          (64*i.val) 64 := by
    intro j hj i
    by_cases old : j<n
    · rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_prior_output_slots
        hash s n target j i holds.counter holds.targetPtr (by omega)
        old targetCase]
      exact holds.targetWords j old i
    · have jeq : j=n := by omega
      subst j
      exact hnew i
  have scratch : ∀ i : Fin 3,
      (tick hash s).getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [stable _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact holds.scratch i
  refine ⟨trace,?_,?_⟩
  · intro more
    have control := next more
    have noCarry := no_carry addressBase limit n params.limitCase
      params.addressAligned more
    have address := GroupedBalancedSignBottomTreeParentAddressData67.tick_address_words
      hash s n target (addressBase+n) holds.counter holds.targetPtr
      (by omega) targetCase (by omega) (by simpa using noCarry)
      holds.address
    exact ⟨control.pc,control.counter,control.count,control.sourcePtr,
      control.targetPtr,heightWord,by simpa [Nat.add_assoc] using address,
      sourceWords,targetWords,scratch⟩
  · intro last
    have control := finish last
    have allTarget : ∀ j, j<limit → ∀ i : Fin 2,
        (tick hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
          (node hash treeBase leafBase leaves (height+1) j).extractLsb'
            (64*i.val) 64 := by
      intro j hj i
      exact targetWords j (by omega) i
    exact ⟨control.pc,control.counter,control.count,control.sourcePtr,
      control.targetPtr,heightWord,sourceWords,allTarget,scratch⟩

theorem fold (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (holds : At hash treeBase leafBase leaves height limit source target
      addressBase n s)
    (nBound : n<limit) :
    ∃ final,
      Trace hash image s (84*(limit-n)) (91*(limit-n))
        (limit-n) (limit-n) final ∧
      Done hash treeBase leafBase leaves height limit source target addressBase
        final := by
  suffices H : ∀ remaining n (s : MachineState), remaining=limit-n →
      n<limit → At hash treeBase leafBase leaves height limit source target
        addressBase n s →
      ∃ final, Trace hash image s (84*remaining) (91*remaining)
        remaining remaining final ∧
        Done hash treeBase leafBase leaves height limit source target
          addressBase final by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨first,next,last⟩ := one_tick hash treeBase leafBase leaves
        height limit source target addressBase n s params holds nBound
      by_cases more : n+1<limit
      · obtain ⟨final,rest,done⟩ := ih (limit-(n+1)) (by omega)
          (n+1) (tick hash s) (by omega) more (next more)
        refine ⟨final,?_,done⟩
        convert first.trans rest using 1 <;> omega
      · have atEnd : n+1=limit := by omega
        refine ⟨tick hash s,?_,last atEnd⟩
        have one : remaining=1 := by omega
        simpa only [one,Nat.mul_one] using first

#print axioms no_carry
#print axioms one_tick
#print axioms fold
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeParentData67

end

/-! Functional first H4 parent and the remaining upper parent row. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstLevelData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperTreeParentData67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev node := GroupedBalancedSignUpperTreeModel67.nodeAt

structure Start (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height limit source target addressBase : Nat)
    (s : MachineState) : Prop where
  ready : GroupedBalancedSignUpperTreeLevelTrace67.Ready heightMax treeBase
    witnessBase height limit source target s
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val)=
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  sourceWords : ∀ j, j<2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val))=
      (node hash treeBase leafBase leaves height j).extractLsb'
        (64*i.val) 64
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val)=
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64

theorem first_source_words (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height limit source target addressBase : Nat)
    (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (start : Start hash treeBase leafBase leaves heightMax witnessBase height
      limit source target addressBase s)
    (heightBound : height<10)
    (witnessBound : witnessBase+16*height+16≤0x80000) :
    ∀ j, j<2*limit → ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (source+16*j+8*i.val))=
        (node hash treeBase leafBase leaves height j).extractLsb'
          (64*i.val) 64 := by
  intro j hj i
  have sourceRange : source ≤
      (BitVec.ofNat 64 (source+16*j+8*i.val)).toNat ∧
      (BitVec.ofNat 64 (source+16*j+8*i.val)).toNat < source+0x4000 := by
    have limitBound : limit ≤ 8 := params.small.2
    rcases params.bases with ⟨rfl,_⟩|⟨rfl,_⟩ <;>
      simp [BitVec.toNat_ofNat] <;> omega
  rw [GroupedBalancedSignUpperTreeFirstControl67.tick_source_frame
    hash s height witnessBase source target _ start.ready.levelWord
    start.ready.witness heightBound witnessBound start.ready.targetPtr
    params.bases sourceRange]
  exact start.sourceWords j hj i

theorem first_address_words (hash : Hash) (s : MachineState)
    (leafBase height witnessBase limit source target addressBase : Nat)
    (levelWord : s.getMem 0x81050=BitVec.ofNat 64 height)
    (witness : s.getMem 0x810f8=BitVec.ofNat 64 witnessBase)
    (heightBound : height<10)
    (witnessBound : witnessBase+16*height+16≤0x80000)
    (destination : s.getMem 0x810c8=BitVec.ofNat 64 target)
    (targetCase : target=0x83000 ∨ target=0x88000)
    (params : Params leafBase height limit source target addressBase)
    (more : 1<limit)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val)=
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (first hash s).getMem (Signing.wordAddress 0x81008 i.val)=
        (BitVec.ofNat 192 (addressBase+1)).extractLsb'
          (64*i.val) 64 := by
  have treeBound : addressBase < 2^160 := by
    have := params.addressBound
    omega
  have noCarry := GroupedBalancedSignUpperTreeParentData67.no_carry
    addressBase limit 0 params.limitCase params.addressAligned more
  intro i
  fin_cases i
  · change (first hash s).getMem 0x81008 = _
    have initial : s.getMem 0x81008=
        (BitVec.ofNat 192 addressBase).extractLsb' 0 64 := by
      simpa [Signing.wordAddress] using address (0 : Fin 3)
    rw [GroupedBalancedSignUpperTreeFirstControl67.tick_address hash s height
      witnessBase target levelWord witness heightBound witnessBound
      destination targetCase,initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.low_step
      addressBase treeBound (by simpa using noCarry)).symm
  · change (first hash s).getMem 0x81010 = _
    have initial : s.getMem 0x81010=
        (BitVec.ofNat 192 addressBase).extractLsb' 64 64 := by
      simpa [Signing.wordAddress] using address (1 : Fin 3)
    rw [GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame
      hash s height witnessBase target 0x81010 levelWord witness heightBound
      witnessBound destination targetCase (by decide) (by decide)
      (by decide) (by decide),initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.middle_step
      addressBase treeBound (by simpa using noCarry)).symm
  · change (first hash s).getMem 0x81018 = _
    have initial : s.getMem 0x81018=
        (BitVec.ofNat 192 addressBase).extractLsb' 128 64 := by
      simpa [Signing.wordAddress] using address (2 : Fin 3)
    rw [GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame
      hash s height witnessBase target 0x81018 levelWord witness heightBound
      witnessBound destination targetCase (by decide) (by decide)
      (by decide) (by decide),initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.high_step
      addressBase treeBound (by simpa using noCarry)).symm

theorem first_result (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height limit source target addressBase : Nat)
    (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (start : Start hash treeBase leafBase leaves heightMax witnessBase height
      limit source target addressBase s)
    (heightBound : height<10)
    (witnessBound : witnessBase+16*height+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    Trace hash image s 113 120 1 1 (first hash s) ∧
    (1<limit → At hash treeBase leafBase leaves height limit source target
      addressBase 1 (first hash s)) ∧
    (limit=1 → Done hash treeBase leafBase leaves height limit source target
      addressBase (first hash s)) := by
  have sourceCase : source=0x83000 ∨ source=0x88000 := by
    rcases params.bases with ⟨h,_⟩|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr h
  have targetCase : target=0x83000 ∨ target=0x88000 := by
    rcases params.bases with ⟨_,h⟩|⟨_,h⟩
    · exact Or.inr h
    · exact Or.inl h
  have trace := GroupedBalancedSignUpperTreeFirstTick67.executes hash s
    height witnessBase source target start.ready.pc start.ready.levelWord
    start.ready.witness heightBound witnessBound witnessAligned
    start.ready.selectedBound start.ready.sourcePtr sourceCase
    start.ready.targetPtr targetCase
  have pc := GroupedBalancedSignUpperTreeFirstControl67.tick_pc hash s height
    witnessBase target start.ready.pc start.ready.levelWord start.ready.witness
    heightBound witnessBound start.ready.targetPtr targetCase
  have count := GroupedBalancedSignUpperTreeFirstControl67.tick_count hash s
    height witnessBase target start.ready.levelWord start.ready.witness
    heightBound witnessBound start.ready.targetPtr targetCase
  have frame (a : Word) (hi : 0x81000 ≤ a.toNat)
      (lo : a.toNat<0x83000) (neD8 : a≠0x810d8)
      (ne08 : a≠0x81008) : (first hash s).getMem a=s.getMem a :=
    GroupedBalancedSignUpperTreeFirstControl67.tick_control_frame hash s
      height witnessBase target a start.ready.levelWord start.ready.witness
      heightBound witnessBound start.ready.targetPtr targetCase hi lo neD8 ne08
  have countWord : (first hash s).getMem 0x810d0=BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact start.ready.count
  have sourcePtr : (first hash s).getMem 0x810c0=BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact start.ready.sourcePtr
  have targetPtr : (first hash s).getMem 0x810c8=BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact start.ready.targetPtr
  have heightWord : (first hash s).getMem 0x81000=
      BitVec.ofNat 64 (treeBase+height) := by
    rw [frame 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact start.ready.treeWord
  have sourceWords := first_source_words hash treeBase leafBase leaves
    heightMax witnessBase height limit source target addressBase s params start
    heightBound witnessBound
  have left : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+8*i.val))=
        (node hash treeBase leafBase leaves height 0).extractLsb'
          (64*i.val) 64 := by
    intro i
    simpa using start.sourceWords 0 (by have := params.small.1; omega) i
  have right : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16+8*i.val))=
        (node hash treeBase leafBase leaves height 1).extractLsb'
          (64*i.val) 64 := by
    intro i
    simpa using start.sourceWords 1 (by have := params.small.1; omega) i
  have output := GroupedBalancedSignUpperTreeFirstData67.tick_output hash s
    height witnessBase (treeBase+height) addressBase source target
    (node hash treeBase leafBase leaves height 0)
    (node hash treeBase leafBase leaves height 1)
    targetCase start.ready.levelWord start.ready.witness heightBound
    witnessBound start.ready.sourcePtr sourceCase start.ready.targetPtr
    start.ready.treeWord start.address left right
  have hnew : ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (target+8*i.val))=
        (node hash treeBase leafBase leaves (height+1) 0).extractLsb'
          (64*i.val) 64 := by
    intro i
    have h := output i
    rw [params.addressDef] at h
    simpa only [node,GroupedBalancedSignUpperTreeModel67.parent,
      Nat.add_zero] using h
  have targetWords : ∀ j, j<1 → ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
        (node hash treeBase leafBase leaves (height+1) j).extractLsb'
          (64*i.val) 64 := by
    intro j hj i
    have jeq : j=0 := by omega
    subst j
    simpa using hnew i
  have scratch : ∀ i : Fin 3,
      (first hash s).getMem (Signing.wordAddress 0x810a8 i.val)=
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact start.scratch i
  refine ⟨trace,?_,?_⟩
  · intro more
    have neq : (1:Word) ≠ BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have oneNat : ((1:Word).toNat)=1 := by decide
      rw [oneNat] at hn
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := params.small.2; omega : limit<2^64)] at hn
      omega
    have pcNext : (first hash s).pc=0x1f08 := by
      rw [start.ready.count] at pc
      simpa only [if_pos neq] using pc
    have address := first_address_words hash s leafBase height witnessBase
      limit source target addressBase start.ready.levelWord
      start.ready.witness heightBound witnessBound start.ready.targetPtr
      targetCase params more start.address
    exact ⟨pcNext,count,countWord,sourcePtr,targetPtr,heightWord,address,
      sourceWords,targetWords,scratch⟩
  · intro one
    have pcDone : (first hash s).pc=0x2058 := by
      rw [start.ready.count,one] at pc
      simpa using pc
    have allTarget : ∀ j, j<limit → ∀ i : Fin 2,
        (first hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val))=
          (node hash treeBase leafBase leaves (height+1) j).extractLsb'
            (64*i.val) 64 := by
      intro j hj i
      exact targetWords j (by omega) i
    exact ⟨pcDone,by simpa [one] using count,countWord,sourcePtr,targetPtr,
      heightWord,sourceWords,allTarget,scratch⟩

theorem one_level (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Reference.Digest)
    (heightMax witnessBase height limit source target addressBase : Nat)
    (s : MachineState)
    (params : Params leafBase height limit source target addressBase)
    (start : Start hash treeBase leafBase leaves heightMax witnessBase height
      limit source target addressBase s)
    (heightBound : height<10)
    (witnessBound : witnessBase+16*height+16≤0x80000)
    (witnessAligned : witnessBase%8=0) :
    ∃ final,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done hash treeBase leafBase leaves height limit source target addressBase
        final := by
  obtain ⟨firstTrace,more,last⟩ := first_result hash treeBase leafBase leaves
    heightMax witnessBase height limit source target addressBase s params
    start heightBound witnessBound witnessAligned
  by_cases gt : 1<limit
  · obtain ⟨final,rest,done⟩ := fold hash treeBase leafBase leaves height
      limit source target addressBase 1 (first hash s) params (more gt) gt
    refine ⟨final,?_,done⟩
    convert firstTrace.trans rest using 1 <;> omega
  · have one : limit=1 := by have := params.small.1; omega
    refine ⟨first hash s,?_,last one⟩
    simpa [one] using firstTrace

#print axioms first_source_words
#print axioms first_result
#print axioms one_level
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeFirstLevelData67
