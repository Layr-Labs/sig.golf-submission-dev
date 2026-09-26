import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentProtected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelTransition67
import SigGolfCandidate.TraceDeterminism

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelProtected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomTreeParentFold67
open GroupedBalancedSignBottomTreeParentLevel67
open GroupedBalancedSignBottomTreeLevelTransition67
open GroupedBalancedSignBottomTreeParentProtected67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image
private abbrev step := GroupedBalancedSignBottomTreeLevelControl67.transitionState

theorem protected_ne (a : Word) (h : Protected a) (b : Nat)
    (hb : 0x20090 ≤ b ∧ b < 0x90000)
    (hb90 : b ≠ 0x81090) (hb98 : b ≠ 0x81098)
    (hba0 : b ≠ 0x810a0) : a ≠ BitVec.ofNat 64 b := by
  rcases h with high | rfl | rfl | rfl | low
  · intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have hc : (0x81090 : Word).toNat = 0x81090 := by decide
    rw [hc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    exact hb90 hn.symm
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have hc : (0x81098 : Word).toNat = 0x81098 := by decide
    rw [hc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    exact hb98 hn.symm
  · intro eq
    have hn := congrArg BitVec.toNat eq
    have hc : (0x810a0 : Word).toNat = 0x810a0 := by decide
    rw [hc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    exact hba0 hn.symm
  · intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega

theorem transition_protected (s : MachineState) (a : Word)
    (safe : Protected a) :
    (step s).getMem a = s.getMem a := by
  exact GroupedBalancedSignBottomTreeLevelData67.frame s a
    (protected_ne a safe 0x810c0 (by decide) (by decide) (by decide) (by decide))
    (protected_ne a safe 0x810c8 (by decide) (by decide) (by decide) (by decide))
    (protected_ne a safe 0x810d0 (by decide) (by decide) (by decide) (by decide))
    (protected_ne a safe 0x81000 (by decide) (by decide) (by decide) (by decide))
    (protected_ne a safe 0x81050 (by decide) (by decide) (by decide) (by decide))

theorem next_start_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (done : Done hash secretKey base height limit source target addressBase s)
    (bound : height < 9) :
    ∃ t,
      Trace hash image s 85 85 0 0 t ∧
      Start hash secretKey base (height+1) (limit/2) target source
        (addressBase/2) t ∧
      (∀ a, Protected a → t.getMem a = s.getMem a) := by
  obtain ⟨t,run,next⟩ :=
    next_start hash secretKey base height limit source target addressBase
      s params done bound
  obtain ⟨transition,between⟩ :=
    transition_continue hash secretKey base height limit source target
      addressBase s params done bound
  obtain ⟨other,prelude,_,_,_,frame⟩ :=
    GroupedBalancedSignBottomTreeLevelPrelude67.level_prelude
      (step s) (BitVec.ofNat 192 addressBase) between.pc between.scratch
  have constructed : Trace hash image s 85 85 0 0 other := by
    simpa only [show 37+48=85 by decide] using
      transition.trans prelude.trace
  have same := Trace.deterministic run constructed
  refine ⟨t,run,next,?_⟩
  intro a safe
  rw [same]
  have p0 : a ≠ 0x81008 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have p1 : a ≠ 0x81010 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have p2 : a ≠ 0x81018 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have p3 : a ≠ 0x810a8 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have p4 : a ≠ 0x810b0 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  have p5 : a ≠ 0x810b8 := protected_ne a safe _ (by decide) (by decide) (by decide) (by decide)
  exact (frame a p0 p1 p2 p3 p4 p5).trans
    (transition_protected s a safe)

theorem height_step_protected (hash : Hash) (secretKey : SecretKey)
    (base height limit source target addressBase : Nat) (s : MachineState)
    (params : Params base height limit source target addressBase)
    (start : Start hash secretKey base height limit source target addressBase s)
    (bound : height < 9) (positive : 0 < limit) :
    ∃ t,
      Trace hash image s
        (113+84*(limit-1)+85) (120+91*(limit-1)+85)
        limit limit t ∧
      Params base (height+1) (limit/2) target source (addressBase/2) ∧
      Start hash secretKey base (height+1) (limit/2) target source
        (addressBase/2) t ∧
      (∀ a, Protected a → t.getMem a = s.getMem a) := by
  obtain ⟨doneState,first,done,firstFrame⟩ :=
    one_level_protected hash secretKey base height limit source target
      addressBase s params start positive
  obtain ⟨t,second,next,secondFrame⟩ :=
    next_start_protected hash secretKey base height limit source target
      addressBase doneState params done bound
  refine ⟨t,?_,params_next base height limit source target addressBase
    params bound,next,?_⟩
  · simpa [Nat.add_assoc] using first.trans second
  · intro a safe
    exact (secondFrame a safe).trans (firstFrame a safe)

#print axioms height_step_protected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelProtected67
