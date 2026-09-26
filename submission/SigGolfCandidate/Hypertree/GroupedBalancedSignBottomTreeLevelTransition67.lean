import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentLevel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelPrelude67
/-! Connecting a completed signer parent table to the next height. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelTransition67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState
private abbrev node := GroupedBalancedSignBottomTreeModel67.levelNode

structure Between (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState) : Prop where
  pc : s.pc = 0x1e04
  sourcePtr : s.getMem 0x810c0 = BitVec.ofNat 64 target
  targetPtr : s.getMem 0x810c8 = BitVec.ofNat 64 source
  count : s.getMem 0x810d0 = BitVec.ofNat 64 (limit/2)
  heightWord : s.getMem 0x81000 = BitVec.ofNat 64 (height+1)
  levelWord : s.getMem 0x81050 = BitVec.ofNat 64 (height+1)
  witnessBase : s.getMem 0x810f8 = 0x20090
  selectedBound : (s.getMem 0x810e8).toNat < 1024
  maxLevel : s.getMem 0x81060 = 10
  scratch : ∀ i : Fin 3,
    s.getMem (Signing.wordAddress 0x810a8 i.val) =
      (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64
  sourceWords : ∀ j, j < limit → ∀ i : Fin 2,
    s.getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64

theorem transition_pc (s : MachineState) (height : Nat)
    (pc : s.pc = 0x2058)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 height)
    (maxLevel : s.getMem 0x81060 = 10)
    (bound : height < 9) : (step s).pc = 0x1e04 := by
  let swapped := GroupedBalancedSignBottomTreeLevelSwap67.swapState s
  let advanced := GroupedBalancedSignBottomTreeLevelAdvance67.advanceState swapped
  have p1 := GroupedBalancedSignBottomTreeLevelSwap67.swap_pc s pc
  have p2 := GroupedBalancedSignBottomTreeLevelAdvance67.advance_pc swapped p1
  have regs := GroupedBalancedSignBottomTreeLevelAdvance67.advance_regs swapped
    (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)
  have witnessWord : swapped.getMem 0x81050 = BitVec.ofNat 64 height := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81050
      (by decide) (by decide)]
    exact levelWord
  have maxWord : swapped.getMem 0x81060 = 10 := by
    rw [GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s 0x81060
      (by decide) (by decide)]
    exact maxLevel
  have ne : BitVec.ofNat 64 height + 1 ≠ (10 : Word) := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    have hSmall : height+1 < 2^64 := by omega
    simp [BitVec.ofNat_add,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hSmall] at hn
    omega
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState advanced).pc = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_pc advanced p2,
    regs.1,regs.2,witnessWord,maxWord,if_pos ne]

theorem transition_continue (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (done : Done hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    Trace hash image s 37 37 0 0 (step s) ∧
    Between hash secretKey base height limit source target addressBase (step s) := by
  have trace : Trace hash image s 37 37 0 0 (step s) :=
    (GroupedBalancedSignBottomTreeLevelControl67.transition_steps s done.pc).trace
  have pc := transition_pc s height done.pc done.levelWord done.maxLevel bound
  have sourcePtr : (step s).getMem 0x810c0 = BitVec.ofNat 64 target := by
    rw [GroupedBalancedSignBottomTreeLevelData67.source,done.targetPtr]
  have targetPtr : (step s).getMem 0x810c8 = BitVec.ofNat 64 source := by
    rw [GroupedBalancedSignBottomTreeLevelData67.target,done.sourcePtr]
  have count : (step s).getMem 0x810d0 = BitVec.ofNat 64 (limit/2) := by
    rw [GroupedBalancedSignBottomTreeLevelData67.count,done.count]
    apply BitVec.eq_of_toNat_eq
    have small : limit < 2^64 := by have := params.limitBound; omega
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt small]
    norm_num
    have halfSmall : limit/2 < 2^64 := by omega
    simpa only [show 2^64 = 18446744073709551616 by decide] using
      (Nat.mod_eq_of_lt halfSmall).symm
  have heightWord : (step s).getMem 0x81000 = BitVec.ofNat 64 (height+1) := by
    rw [GroupedBalancedSignBottomTreeLevelData67.height,done.heightWord]
    simp [BitVec.ofNat_add]
  have levelWord : (step s).getMem 0x81050 = BitVec.ofNat 64 (height+1) := by
    rw [GroupedBalancedSignBottomTreeLevelData67.witness_level,done.levelWord]
    simp [BitVec.ofNat_add]
  have frame (a : Word) (h0 : a ≠ 0x810c0) (h1 : a ≠ 0x810c8)
      (h2 : a ≠ 0x810d0) (h3 : a ≠ 0x81000) (h4 : a ≠ 0x81050) :
      (step s).getMem a = s.getMem a :=
    GroupedBalancedSignBottomTreeLevelData67.frame s a h0 h1 h2 h3 h4
  have witnessBase : (step s).getMem 0x810f8 = 0x20090 := by
    rw [frame 0x810f8 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact done.witnessBase
  have selectedBound : ((step s).getMem 0x810e8).toNat < 1024 := by
    rw [frame 0x810e8 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact done.selectedBound
  have maxLevel : (step s).getMem 0x81060 = 10 := by
    rw [frame 0x81060 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact done.maxLevel
  have scratch : ∀ i : Fin 3,
      (step s).getMem (Signing.wordAddress 0x810a8 i.val) =
        (BitVec.ofNat 192 addressBase).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)]
    exact done.scratch i
  have sourceWords : ∀ j, j < limit → ∀ i : Fin 2,
      (step s).getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    have ne (a : Nat) (ha : a < 0x83000) :
        BitVec.ofNat 64 (target+16*j+8*i.val) ≠ BitVec.ofNat 64 a := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have targetMin : 0x83000 ≤ target := by
        rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
      have targetMax : target ≤ 0x88000 := by
        rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt
        (by have := params.limitBound; omega : target+16*j+8*i.val < 2^64),
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a < 2^64)] at hn
      omega
    rw [frame _ (ne _ (by decide)) (ne _ (by decide))
      (ne _ (by decide)) (ne _ (by decide)) (ne _ (by decide))]
    exact done.targetWords j hj i
  exact ⟨trace,⟨pc,sourcePtr,targetPtr,count,heightWord,levelWord,
    witnessBase,selectedBound,maxLevel,scratch,sourceWords⟩⟩

theorem even_limit (height limit : Nat)
    (bound : height < 9) (limitDef : limit = 512/2^height) :
    2*(limit/2)=limit := by
  subst limit
  interval_cases height <;> norm_num at *

theorem next_prelude (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (between : Between hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    ∃ t,
      Trace hash image s 48 48 0 0 t ∧
      GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
        base (height+1) (limit/2) target source (addressBase/2) t := by
  obtain ⟨t,steps,pc,addressWords,scratchWords,frame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      s (BitVec.ofNat 192 addressBase) between.pc between.scratch
  have trace : Trace hash image s 48 48 0 0 t := steps.trace
  have addressSmall : addressBase < 2^192 := by
    have hb := params.addressBound
    omega
  have shifted : (BitVec.ofNat 192 addressBase >>> 1) =
      BitVec.ofNat 192 (addressBase/2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have preserve (a : Word)
      (h0 : a ≠ 0x81008) (h1 : a ≠ 0x81010) (h2 : a ≠ 0x81018)
      (h3 : a ≠ 0x810a8) (h4 : a ≠ 0x810b0) (h5 : a ≠ 0x810b8) :
      t.getMem a = s.getMem a := frame a h0 h1 h2 h3 h4 h5
  have levelWord : t.getMem 0x81050 = BitVec.ofNat 64 (height+1) := by
    rw [preserve 0x81050 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.levelWord
  have witnessBase : t.getMem 0x810f8 = 0x20090 := by
    rw [preserve 0x810f8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.witnessBase
  have selectedBound : (t.getMem 0x810e8).toNat < 1024 := by
    rw [preserve 0x810e8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.selectedBound
  have sourcePtr : t.getMem 0x810c0 = BitVec.ofNat 64 target := by
    rw [preserve 0x810c0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.sourcePtr
  have targetPtr : t.getMem 0x810c8 = BitVec.ofNat 64 source := by
    rw [preserve 0x810c8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.targetPtr
  have count : t.getMem 0x810d0 = BitVec.ofNat 64 (limit/2) := by
    rw [preserve 0x810d0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.count
  have heightWord : t.getMem 0x81000 = BitVec.ofNat 64 (height+1) := by
    rw [preserve 0x81000 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.heightWord
  have maxLevel : t.getMem 0x81060 = 10 := by
    rw [preserve 0x81060 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact between.maxLevel
  have sourceWords : ∀ j, j < 2*(limit/2) → ∀ i : Fin 2,
      t.getMem (BitVec.ofNat 64 (target+16*j+8*i.val)) =
      (node hash secretKey base (height+1) j).extractLsb' (64*i.val) 64 := by
    intro j hj i
    have jBound : j < limit := by rw [←even_limit height limit bound params.limitDef]; exact hj
    have targetMin : 0x83000 ≤ target := by
      rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
    have targetMax : target ≤ 0x88000 := by
      rcases params.bases with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
    have limitBound := params.limitBound
    have small : target+16*j+8*i.val < 2^64 := by omega
    have nat : (BitVec.ofNat 64 (target+16*j+8*i.val)).toNat =
        target+16*j+8*i.val := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have ne (a : Word) (ha : a.toNat < 0x83000) :
        BitVec.ofNat 64 (target+16*j+8*i.val) ≠ a := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      rw [nat] at hn
      omega
    rw [preserve _ (ne 0x81008 (by decide)) (ne 0x81010 (by decide))
      (ne 0x81018 (by decide)) (ne 0x810a8 (by decide))
      (ne 0x810b0 (by decide)) (ne 0x810b8 (by decide))]
    exact between.sourceWords j jBound i
  have address : ∀ i : Fin 3,
      t.getMem (Signing.wordAddress 0x81008 i.val) =
      (BitVec.ofNat 192 (addressBase/2)).extractLsb' (64*i.val) 64 := by
    intro i
    rw [addressWords i,shifted]
  have scratch : ∀ i : Fin 3,
      t.getMem (Signing.wordAddress 0x810a8 i.val) =
      (BitVec.ofNat 192 (addressBase/2)).extractLsb' (64*i.val) 64 := by
    intro i
    rw [scratchWords i,shifted]
  exact ⟨t,trace,⟨pc,levelWord,witnessBase,selectedBound,sourcePtr,targetPtr,
    count,heightWord,address,sourceWords,scratch,maxLevel⟩⟩

theorem next_start (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (done : Done hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    ∃ t,
      Trace hash image s 85 85 0 0 t ∧
      GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
        base (height+1) (limit/2) target source (addressBase/2) t := by
  obtain ⟨first,between⟩ :=
    transition_continue hash secretKey base height limit source target
      addressBase s params done bound
  obtain ⟨t,second,start⟩ :=
    next_prelude hash secretKey base height limit source target addressBase
      (step s) params between bound
  exact ⟨t,by simpa only [show 37+48=85 by decide] using first.trans second,start⟩

theorem params_next (base height limit source target addressBase : Nat)
    (params : Params base height limit source target addressBase)
    (bound : height < 9) :
    Params base (height+1) (limit/2) target source (addressBase/2) := by
  have halfLimit : 2*(limit/2)=limit := even_limit height limit bound params.limitDef
  have limitNext : limit/2 = 512 / 2^(height+1) := by
    rw [params.limitDef]
    interval_cases height <;> norm_num at *
  have addressNext : addressBase/2 = base / 2^((height+1)+1) := by
    rw [params.addressDef]
    rw [Nat.div_div_eq_div_mul]
    simp only [pow_succ]
  have alignedNext : (addressBase/2) % (limit/2) = 0 := by
    obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero params.addressAligned
    rw [hk,←halfLimit]
    have div : (2*(limit/2)*k)/2 = (limit/2)*k := by
      rw [mul_assoc]
      simp [Nat.mul_comm]
    rw [div]
    simp
  have boundNext : addressBase/2 + limit/2 < 2^160 := by
    have aLe := Nat.div_le_self addressBase 2
    have lLe := Nat.div_le_self limit 2
    have old := params.addressBound
    omega
  refine ⟨by omega,limitNext,by have := params.limitBound; omega,
    params.baseAligned,addressNext,alignedNext,boundNext,?_⟩
  rcases params.bases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

theorem height_step (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
      base height limit source target addressBase s)
    (bound : height < 9) (positive : 0 < limit) :
    ∃ next,
      Trace hash image s (113+84*(limit-1)+85) (120+91*(limit-1)+85)
        limit limit next ∧
      Params base (height+1) (limit/2) target source (addressBase/2) ∧
      GroupedBalancedSignBottomTreeParentLevel67.Start hash secretKey
        base (height+1) (limit/2) target source (addressBase/2) next := by
  obtain ⟨doneState,first,done⟩ :=
    GroupedBalancedSignBottomTreeParentLevel67.one_level hash secretKey
      base height limit source target addressBase s params start positive
  obtain ⟨next,second,nextStart⟩ :=
    next_start hash secretKey base height limit source target addressBase
      doneState params done bound
  refine ⟨next,?_,params_next base height limit source target addressBase
    params bound,nextStart⟩
  convert first.trans second using 1 <;> omega

#print axioms transition_continue
#print axioms next_prelude
#print axioms next_start
#print axioms params_next
#print axioms height_step
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelTransition67
