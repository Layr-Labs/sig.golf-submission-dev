import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAddressData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeModel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeFirstTickControl67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentFold67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67. -/
section
/-! Inductive machine invariant for the repeated bottom-tree parent ticks. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentFold67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev F := GroupedBalancedSignBottomTreeInnerTickFrame67.tickState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode

structure At (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat)
    (s : MachineState) : Prop where
  pc : s.pc = 0x1f08
  counter : s.getMem 0x810d8 = BitVec.ofNat 64 n
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target
  heightWord : s.getMem 0x81000 = BitVec.ofNat 64 height
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 (addressBase+n)).extractLsb' (64*i.val) 64
  sourceWords : ∀ j, j < 2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) =
      (node hash secretKey base height j).extractLsb' (64*i.val) 64
  targetWords : ∀ j, j < n → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64
  witnessBase : s.getMem 0x810f8 = 0x20090
  selectedBound : (s.getMem 0x810e8).toNat < 1024
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val) =
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  maxLevel : s.getMem 0x81060 = 10
  levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height

structure Done (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x2058
  counter : s.getMem 0x810d8 = BitVec.ofNat 64 limit
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target
  heightWord : s.getMem 0x81000 = BitVec.ofNat 64 height
  sourceWords : ∀ j, j < 2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) =
      (node hash secretKey base height j).extractLsb' (64*i.val) 64
  targetWords : ∀ j, j < limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64
  witnessBase : s.getMem 0x810f8 = 0x20090
  selectedBound : (s.getMem 0x810e8).toNat < 1024
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val) =
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  maxLevel : s.getMem 0x81060 = 10
  levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height

theorem child_left (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) (i : Fin 2) :
    s.getMem
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 (8*i.val)) =
      (node hash secretKey base height (2*n)).extractLsb' (64*i.val) 64 := by
  rw [GroupedBalancedSignBottomTreePointerData67.pair_reg_nat s n source
    holds.counter holds.sourcePtr]
  have h := holds.sourceWords (2*n) (by omega) i
  have hn : 16*(2*n)=32*n := by omega
  rw [hn] at h
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using h

theorem child_right (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) (i : Fin 2) :
    s.getMem
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 (16+8*i.val)) =
      (node hash secretKey base height (2*n+1)).extractLsb' (64*i.val) 64 := by
  rw [GroupedBalancedSignBottomTreePointerData67.pair_reg_nat s n source
    holds.counter holds.sourcePtr]
  have h := holds.sourceWords (2*n+1) (by omega) i
  have hn : 16*(2*n+1)=32*n+16 := by omega
  rw [hn] at h
  simpa [BitVec.ofNat_add,BitVec.add_assoc] using h

structure Params (base height limit source target addressBase : Nat) : Prop where
  heightBound : height < 10
  limitDef : limit = 512 / 2^height
  limitBound : limit ≤ 512
  baseAligned : base % 2^10 = 0
  addressDef : addressBase = base / 2^(height+1)
  addressAligned : addressBase % limit = 0
  addressBound : addressBase + limit < 2^160
  bases : (source = 0x83000 ∧ target = 0x88000) ∨
    (source = 0x88000 ∧ target = 0x83000)

theorem one_tick (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) :
    Trace hash image s 84 91 1 1 (F hash s) ∧
    (n+1 < limit →
      At hash secretKey base height limit source target addressBase (n+1) (F hash s)) ∧
    (n+1 = limit →
      Done hash secretKey base height limit source target addressBase (F hash s)) := by
  have limitBound := params.limitBound
  have addressBound := params.addressBound
  have countBound : n < 512 := by omega
  have targetCase : target = 0x83000 ∨ target = 0x88000 := by
    rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have sourceCase : source = 0x83000 ∨ source = 0x88000 := by
    rcases params.bases with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have trace := GroupedBalancedSignBottomTreeInnerTickData67.tick_trace
    hash s n source target holds.pc holds.counter holds.sourcePtr holds.targetPtr
    countBound sourceCase targetCase
  have hpc := GroupedBalancedSignBottomTreeInnerTickData67.tick_pc
    hash s n target holds.pc holds.counter holds.targetPtr countBound targetCase
  have hcount : (F hash s).getMem 0x810d8 = BitVec.ofNat 64 (n+1) := by
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_count
      hash s n target holds.counter holds.targetPtr countBound targetCase,
      holds.counter]
    simp [BitVec.ofNat_add]
  have frame (a : Word) (hi : 0x81000 ≤ a.toNat) (lo : a.toNat < 0x83000)
      (ne08 : a ≠ 0x81008) (ned8 : a ≠ 0x810d8) :
      (F hash s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeInnerTickFrame67.tick_control_frame
      hash s n target a holds.counter holds.targetPtr countBound targetCase
      hi lo ne08 ned8
  have hlimit : (F hash s).getMem 0x810d0 = BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact holds.count
  have hsource : (F hash s).getMem 0x810c0 = BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact holds.sourcePtr
  have htarget : (F hash s).getMem 0x810c8 = BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact holds.targetPtr
  have hheight : (F hash s).getMem 0x81000 = BitVec.ofNat 64 height := by
    rw [frame 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact holds.heightWord
  have hsourceWords : ∀ j, j < 2*limit → ∀ i : Fin 2,
      (F hash s).getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) =
      (node hash secretKey base height j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_source_slots
      hash s n source target j i holds.counter holds.targetPtr countBound
      (by omega) params.bases]
    exact holds.sourceWords j hj i
  have output := GroupedBalancedSignBottomTreeInnerTickData67.output_node_at
    hash s n target height (addressBase+n)
    (node hash secretKey base height (2*n))
    (node hash secretKey base height (2*n+1))
    holds.counter holds.targetPtr countBound targetCase holds.heightWord holds.address
    (child_left hash secretKey base height limit source target addressBase n s
      holds nBound)
    (child_right hash secretKey base height limit source target addressBase n s
      holds nBound)
  have hnew : ∀ i : Fin 2,
      (F hash s).getMem (BitVec.ofNat 64 (target+16*n+8*i.val)) =
        (node hash secretKey base (height+1) n).extractLsb' (64*i.val) 64 := by
    intro i
    change (F hash s).getMem (BitVec.ofNat 64 (target+16*n+8*i.val)) =
      (GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey base
        (height+1) n).extractLsb' (64*i.val) 64
    rw [GroupedBalancedSignBottomTreeModel67.parent_node
      hash secretKey base height n params.baseAligned params.heightBound]
    simpa only [params.addressDef] using output i
  have htargetWords : ∀ j, j < n+1 → ∀ i : Fin 2,
      (F hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    by_cases old : j < n
    · rw [GroupedBalancedSignBottomTreeInnerTickFrame67.tick_prior_output_slots
        hash s n target j i holds.counter holds.targetPtr countBound old targetCase]
      exact holds.targetWords j old i
    · have jeq : j = n := by omega
      subst j
      exact hnew i
  have hwitness : (F hash s).getMem 0x810f8 = 0x20090 := by
    rw [frame 0x810f8 (by decide) (by decide) (by decide) (by decide)]
    exact holds.witnessBase
  have hselected : ((F hash s).getMem 0x810e8).toNat < 1024 := by
    rw [frame 0x810e8 (by decide) (by decide) (by decide) (by decide)]
    exact holds.selectedBound
  have hscratch : ∀ i : Fin 3,
      (F hash s).getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact holds.scratch i
  have hmax : (F hash s).getMem 0x81060 = 10 := by
    rw [frame 0x81060 (by decide) (by decide) (by decide) (by decide)]
    exact holds.maxLevel
  have hlevel : (F hash s).getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [frame 0x81050 (by decide) (by decide) (by decide) (by decide)]
    exact holds.levelWord
  have hcountEq : s.getMem 0x810d8 + 1 = BitVec.ofNat 64 (n+1) := by
    rw [holds.counter]
    simp [BitVec.ofNat_add]
  constructor
  · exact trace
  constructor
  · intro next
    have neq : BitVec.ofNat 64 (n+1) ≠ BitVec.ofNat 64 limit := by
      intro h
      have hn := congrArg BitVec.toNat h
      have smallN : n+1 < 2^64 := by omega
      have smallLimit : limit < 2^64 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt smallN,
        Nat.mod_eq_of_lt smallLimit] at hn
      omega
    have hpcCont : (F hash s).pc = 0x1f08 := by
      rw [hcountEq,holds.count] at hpc
      simpa only [if_pos neq] using hpc
    have treeBound : addressBase+n < 2^160 := by omega
    have noCarry := GroupedBalancedSignBottomTreeParentNoCarry67.no_carry
      addressBase height n params.heightBound
      (by simpa [params.limitDef] using params.addressAligned) (by simpa [params.limitDef] using next)
    have haddr := GroupedBalancedSignBottomTreeParentAddressData67.tick_address_words
      hash s n target (addressBase+n) holds.counter holds.targetPtr countBound
      targetCase treeBound noCarry holds.address
    exact ⟨hpcCont,hcount,hlimit,hsource,htarget,hheight,by simpa [Nat.add_assoc] using haddr,
      hsourceWords,htargetWords,hwitness,hselected,hscratch,hmax,hlevel⟩
  · intro last
    have eq : BitVec.ofNat 64 (n+1) = BitVec.ofNat 64 limit := by rw [last]
    have hpcDone : (F hash s).pc = 0x2058 := by
      rw [hcountEq,holds.count] at hpc
      simpa only [eq, ne_eq, not_true_eq_false, ite_false] using hpc
    have lastCounter : (F hash s).getMem 0x810d8 = BitVec.ofNat 64 limit := by
      simpa only [last] using hcount
    have allTarget : ∀ j, j < limit → ∀ i : Fin 2,
      (F hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
      intro j hj
      exact htargetWords j (by omega)
    exact ⟨hpcDone,lastCounter,hlimit,hsource,htarget,hheight,hsourceWords,allTarget,
      hwitness,hselected,hscratch,hmax,hlevel⟩

theorem fold (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase n : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (holds : At hash secretKey base height limit source target addressBase n s)
    (nBound : n < limit) :
    ∃ final,
      Trace hash image s (84*(limit-n)) (91*(limit-n)) (limit-n) (limit-n) final ∧
      Done hash secretKey base height limit source target addressBase final := by
  suffices H : ∀ remaining n (s : MachineState), remaining = limit-n →
      n < limit → At hash secretKey base height limit source target addressBase n s →
      ∃ final,
        Trace hash image s (84*remaining) (91*remaining) remaining remaining final ∧
        Done hash secretKey base height limit source target addressBase final by
    exact H (limit-n) n s rfl nBound holds
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
      intro n s remEq nBound holds
      obtain ⟨first, next, last⟩ :=
        one_tick hash secretKey base height limit source target addressBase n s
          params holds nBound
      by_cases more : n+1 < limit
      · obtain ⟨final,rest,finished⟩ :=
          ih (limit-(n+1)) (by omega) (n+1) (F hash s)
            (by omega) more (next more)
        refine ⟨final,?_,finished⟩
        convert first.trans rest using 1 <;> omega
      · have atEnd : n+1=limit := by omega
        refine ⟨F hash s,?_,last atEnd⟩
        have one : remaining = 1 := by omega
        simpa only [one, Nat.mul_one] using first

#print axioms one_tick
#print axioms fold

end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentFold67

end

/-! A complete signing bottom-tree parent level: first tick and remaining parent fold. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev first := GroupedBalancedSignBottomTreeFirstTickData67.tickState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode
open GroupedBalancedSignBottomTreeParentFold67

structure Start (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1e94
  levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height
  witnessBase : s.getMem 0x810f8 = 0x20090
  selectedBound : (s.getMem 0x810e8).toNat < 1024
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 source
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 target
  count : s.getMem 0x810d0 = BitVec.ofNat 64 limit
  heightWord : s.getMem 0x81000 = BitVec.ofNat 64 height
  address : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  sourceWords : ∀ j, j < 2*limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) =
      (node hash secretKey base height j).extractLsb' (64*i.val) 64
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val) =
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  maxLevel : s.getMem 0x81060 = 10

private theorem target_case (source target : Nat)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000)) :
    target = 0x83000 ∨ target = 0x88000 := by
  rcases bases with ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem source_case (source target : Nat)
    (bases : (source = 0x83000 ∧ target = 0x88000) ∨
      (source = 0x88000 ∧ target = 0x83000)) :
    source = 0x83000 ∨ source = 0x88000 := by
  rcases bases with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem first_output_frame (hash : Hash) (s : MachineState)
    (height target : Nat) (i : Fin 2)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (heightBound : height < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000) :
    (first hash s).getMem (BitVec.ofNat 64 (target+8*i.val)) =
      (GroupedBalancedSignBottomTreeFirstTickData67.stored hash s).getMem
        (BitVec.ofNat 64 (target+8*i.val)) := by
  let a := BitVec.ofNat 64 (target+8*i.val)
  have nat : a.toNat = target+8*i.val := by
    rcases targetCase with rfl | rfl <;> fin_cases i <;> decide
  have ne08 : a ≠ 0x81008 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [nat] at hn; simp at hn; omega
  have ned8 : a ≠ 0x810d8 := by
    intro eq; have hn := congrArg BitVec.toNat eq; rw [nat] at hn; simp at hn; omega
  change (GroupedBalancedSignBottomTreeParentControl67.branchState
    (GroupedBalancedSignBottomTreeFirstTickData67.advanced hash s)).getMem a = _
  rw [GroupedBalancedSignBottomTreeParentControl67.branch_frame,
    GroupedBalancedSignBottomTreeFirstTickData67.advanced,
    GroupedBalancedSignBottomTreeParentControl67.advance_frame _ a ne08 ned8]

theorem first_source_words (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s) :
    ∀ j, j < 2*limit → ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (source+16*j+8*i.val)) =
        (node hash secretKey base height j).extractLsb' (64*i.val) 64 := by
  intro j hj i
  have sourceCase := source_case source target params.bases
  have targetCase := target_case source target params.bases
  have slotBound : j < 1024 := by have := params.limitBound; omega
  have sourceRange : source ≤
      (BitVec.ofNat 64 (source+16*j+8*i.val)).toNat ∧
      (BitVec.ofNat 64 (source+16*j+8*i.val)).toNat < source+0x4000 := by
    rcases sourceCase with rfl | rfl <;>
      simp [BitVec.toNat_ofNat] <;> omega
  rw [GroupedBalancedSignBottomTreeFirstTickData67.tick_source_frame
    hash s height source target _ start.levelWord start.witnessBase
    params.heightBound start.targetPtr params.bases sourceRange]
  exact start.sourceWords j hj i

theorem first_address_words (hash : Hash) (s : MachineState)
    (height limit target addressBase : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (heightBound : height < 10)
    (destination : s.getMem 0x810c8 = BitVec.ofNat 64 target)
    (targetCase : target = 0x83000 ∨ target = 0x88000)
    (limitDef : limit = 512/2^height)
    (aligned : addressBase % limit = 0)
    (addressBound : addressBase+limit < 2^160)
    (more : 1 < limit)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (first hash s).getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 (addressBase+1)).extractLsb' (64*i.val) 64 := by
  have treeBound : addressBase < 2^160 := by omega
  have noCarry := GroupedBalancedSignBottomTreeParentNoCarry67.no_carry
    addressBase height 0 heightBound (by simpa [limitDef] using aligned)
      (by simpa [limitDef] using more)
  intro i
  fin_cases i
  · change (first hash s).getMem 0x81008 = _
    have initial : s.getMem 0x81008 =
        (BitVec.ofNat 192 addressBase).extractLsb' 0 64 := by
      simpa [Signing.wordAddress] using address (0 : Fin 3)
    rw [GroupedBalancedSignBottomTreeFirstTickData67.tick_address
      hash s height target levelWord witnessBase heightBound destination
      targetCase,initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.low_step
      addressBase treeBound (by simpa using noCarry)).symm
  · change (first hash s).getMem 0x81010 = _
    have initial : s.getMem 0x81010 =
        (BitVec.ofNat 192 addressBase).extractLsb' 64 64 := by
      simpa [Signing.wordAddress] using address (1 : Fin 3)
    rw [GroupedBalancedSignBottomTreeFirstTickData67.tick_control_frame
      hash s height target 0x81010 levelWord witnessBase heightBound
      destination targetCase (by decide) (by decide) (by decide) (by decide),
      initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.middle_step
      addressBase treeBound (by simpa using noCarry)).symm
  · change (first hash s).getMem 0x81018 = _
    have initial : s.getMem 0x81018 =
        (BitVec.ofNat 192 addressBase).extractLsb' 128 64 := by
      simpa [Signing.wordAddress] using address (2 : Fin 3)
    rw [GroupedBalancedSignBottomTreeFirstTickData67.tick_control_frame
      hash s height target 0x81018 levelWord witnessBase heightBound
      destination targetCase (by decide) (by decide) (by decide) (by decide),
      initial]
    simpa using (GroupedBalancedSignBottomTreeParentAddressStep67.high_step
      addressBase treeBound (by simpa using noCarry)).symm

theorem first_result (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (positive : 0 < limit) :
    Trace hash image s 113 120 1 1 (first hash s) ∧
    (1 < limit →
      At hash secretKey base height limit source target addressBase 1 (first hash s)) ∧
    (limit = 1 →
      Done hash secretKey base height limit source target addressBase (first hash s)) := by
  have sourceCase := source_case source target params.bases
  have targetCase := target_case source target params.bases
  have trace := GroupedBalancedSignBottomTreeFirstTickReady67.executes
    hash s height source target start.pc start.levelWord start.witnessBase
    params.heightBound start.selectedBound start.sourcePtr sourceCase
    start.targetPtr targetCase
  have pc := GroupedBalancedSignBottomTreeFirstTickControl67.tick_pc
    hash s height target start.pc start.levelWord start.witnessBase
    params.heightBound start.targetPtr targetCase
  have count := GroupedBalancedSignBottomTreeFirstTickData67.tick_count
    hash s height target start.levelWord start.witnessBase params.heightBound
      start.targetPtr targetCase
  have frame (a : Word) (hi : 0x81000 ≤ a.toNat) (lo : a.toNat < 0x83000)
      (ned8 : a ≠ 0x810d8) (ne08 : a ≠ 0x81008) :
      (first hash s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeFirstTickData67.tick_control_frame
      hash s height target a start.levelWord start.witnessBase params.heightBound
      start.targetPtr targetCase hi lo ned8 ne08
  have hlimit : (first hash s).getMem 0x810d0 = BitVec.ofNat 64 limit := by
    rw [frame 0x810d0 (by decide) (by decide) (by decide) (by decide)]
    exact start.count
  have hsource : (first hash s).getMem 0x810c0 = BitVec.ofNat 64 source := by
    rw [frame 0x810c0 (by decide) (by decide) (by decide) (by decide)]
    exact start.sourcePtr
  have htarget : (first hash s).getMem 0x810c8 = BitVec.ofNat 64 target := by
    rw [frame 0x810c8 (by decide) (by decide) (by decide) (by decide)]
    exact start.targetPtr
  have hheight : (first hash s).getMem 0x81000 = BitVec.ofNat 64 height := by
    rw [frame 0x81000 (by decide) (by decide) (by decide) (by decide)]
    exact start.heightWord
  have hsourceWords := first_source_words hash secretKey base height limit
    source target addressBase s params start
  have left : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+8*i.val)) =
      (node hash secretKey base height 0).extractLsb' (64*i.val) 64 := by
    intro i
    simpa using start.sourceWords 0 (by omega) i
  have right : ∀ i : Fin 2,
      s.getMem (BitVec.ofNat 64 (source+16+8*i.val)) =
      (node hash secretKey base height 1).extractLsb' (64*i.val) 64 := by
    intro i
    simpa using start.sourceWords 1 (by omega) i
  have stored := GroupedBalancedSignBottomTreeFirstTickData67.output_node
    hash s height addressBase source target
    (node hash secretKey base height 0) (node hash secretKey base height 1)
    start.levelWord start.witnessBase params.heightBound start.sourcePtr
    sourceCase start.targetPtr start.heightWord start.address left right
  have hnew : ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (target+8*i.val)) =
      (node hash secretKey base (height+1) 0).extractLsb' (64*i.val) 64 := by
    intro i
    have full := (first_output_frame hash s height target i start.levelWord
      start.witnessBase params.heightBound start.targetPtr targetCase).trans (stored i)
    change (first hash s).getMem (BitVec.ofNat 64 (target+8*i.val)) =
      (GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey base
        (height+1) 0).extractLsb' (64*i.val) 64
    rw [GroupedBalancedSignBottomTreeModel67.parent_node
      hash secretKey base height 0 params.baseAligned params.heightBound]
    simpa only [params.addressDef, Nat.add_zero] using full
  have targetWords : ∀ j, j < 1 → ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    have jeq : j=0 := by omega
    subst j
    simpa using hnew i
  have hwitness : (first hash s).getMem 0x810f8 = 0x20090 := by
    rw [frame 0x810f8 (by decide) (by decide) (by decide) (by decide)]
    exact start.witnessBase
  have hselected : ((first hash s).getMem 0x810e8).toNat < 1024 := by
    rw [frame 0x810e8 (by decide) (by decide) (by decide) (by decide)]
    exact start.selectedBound
  have hscratch : ∀ i : Fin 3,
      (first hash s).getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact start.scratch i
  have hmax : (first hash s).getMem 0x81060 = 10 := by
    rw [frame 0x81060 (by decide) (by decide) (by decide) (by decide)]
    exact start.maxLevel
  have hlevel : (first hash s).getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [frame 0x81050 (by decide) (by decide) (by decide) (by decide)]
    exact start.levelWord
  constructor
  · exact trace
  constructor
  · intro more
    have ne : (1 : Word) ≠ BitVec.ofNat 64 limit := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have bound := params.limitBound
      have oneNat : ((1 : Word).toNat) = 1 := by decide
      rw [oneNat] at hn
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : limit < 2^64)] at hn
      omega
    have hpc : (first hash s).pc = 0x1f08 := by
      rw [start.count] at pc
      simpa only [if_pos ne] using pc
    have addr := first_address_words hash s height limit target addressBase
      start.levelWord start.witnessBase params.heightBound start.targetPtr
      targetCase params.limitDef params.addressAligned params.addressBound
      more start.address
    exact ⟨hpc,count,hlimit,hsource,htarget,hheight,addr,hsourceWords,targetWords,
      hwitness,hselected,hscratch,hmax,hlevel⟩
  · intro one
    have hpc : (first hash s).pc = 0x2058 := by
      rw [start.count,one] at pc
      simpa using pc
    have countOne : (first hash s).getMem 0x810d8 = BitVec.ofNat 64 limit := by
      simpa [one] using count
    have allTarget : ∀ j, j < limit → ∀ i : Fin 2,
      (first hash s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
      intro j hj
      exact targetWords j (by omega)
    exact ⟨hpc,countOne,hlimit,hsource,htarget,hheight,hsourceWords,allTarget,
      hwitness,hselected,hscratch,hmax,hlevel⟩

theorem one_level (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (positive : 0 < limit) :
    ∃ final,
      Trace hash image s (113+84*(limit-1)) (120+91*(limit-1))
        limit limit final ∧
      Done hash secretKey base height limit source target addressBase final := by
  obtain ⟨firstTrace, hcontinue, finish⟩ :=
    first_result hash secretKey base height limit source target addressBase
      s params start positive
  by_cases more : 1 < limit
  · obtain ⟨final, rest, done⟩ :=
      GroupedBalancedSignBottomTreeParentFold67.fold hash secretKey base
        height limit source target addressBase 1 (first hash s) params
        (hcontinue more) more
    refine ⟨final,?_,done⟩
    convert firstTrace.trans rest using 1 <;> omega
  · have one : limit=1 := by omega
    refine ⟨first hash s,?_,finish one⟩
    simpa [one] using firstTrace

#print axioms first_address_words
#print axioms first_result
#print axioms one_level

#print axioms first_output_frame
#print axioms first_source_words
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
