import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHeader67
import SigGolfCandidate.Hypertree.KeygenNode
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodePrelude67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenNodeHash67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPrelude67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNode67. -/
section
/-! The direct67 keygen node prelude copies four child words into its hash buffer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenNodePrelude67
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem prelude_mem (s : MachineState) (a : Word) (n src : Nat)
    (nBound : n < 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (index : s.getMem 0x81040 = BitVec.ofNat 64 n)
    (source : s.getMem 0x81078 = BitVec.ofNat 64 src) :
    (preludeState s).getMem a =
      if a = 0x80038 then
        s.getMem ((s.getMem 0x81040 <<< 5) + s.getMem 0x81078 + 24)
      else if a = 0x80030 then
        s.getMem ((s.getMem 0x81040 <<< 5) + s.getMem 0x81078 + 16)
      else if a = 0x80028 then
        s.getMem ((s.getMem 0x81040 <<< 5) + s.getMem 0x81078 + 8)
      else if a = 0x80020 then
        s.getMem ((s.getMem 0x81040 <<< 5) + s.getMem 0x81078)
      else if a = 0x81008 then s.getMem 0x81040
      else s.getMem a := by
  have srcEq (off : Nat) :
      (s.getMem 0x81040 <<< 5) + s.getMem 0x81078 +
          BitVec.ofNat 64 off = BitVec.ofNat 64 (src+32*n+off) := by
    rw [index,source,KeygenDomain.shift_ofNat]
    simp only [show 2^5=32 by decide,←BitVec.ofNat_add]
    congr 1
    omega
  have neSrc (off : Nat) (offBound : off ≤ 24) :
      (s.getMem 0x81040 <<< 5) + s.getMem 0x81078 +
          BitVec.ofNat 64 off ≠ 0x81008 := by
    rw [srcEq]
    intro eq
    have hn := congrArg BitVec.toNat eq
    have small : src+32*n+off<2^64 := by
      rcases srcCase with rfl | rfl <;> omega
    have low : 0x82000≤src+32*n+off := by
      rcases srcCase with rfl | rfl <;> omega
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at hn
    have target : (0x81008 : Word).toNat=0x81008 := by decide
    rw [target] at hn
    omega
  have ne0 : (s.getMem 0x81040 <<< 5) + s.getMem 0x81078 ≠ 0x81008 := by
    simpa using neSrc 0 (by decide)
  have ne8 := neSrc 8 (by decide)
  have ne16 := neSrc 16 (by decide)
  have ne24 := neSrc 24 (by decide)
  simp [preludeState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]
  split_ifs <;> simp_all

theorem source_address (s : MachineState) (n src : Nat)
    (index : s.getMem 0x81040 = BitVec.ofNat 64 n)
    (source : s.getMem 0x81078 = BitVec.ofNat 64 src)
    (i : Fin 4) :
    (s.getMem 0x81040 <<< 5) + s.getMem 0x81078 +
      BitVec.ofNat 64 (8*i.val) =
      Signing.wordAddress (src+32*n) i.val := by
  rw [index,source,KeygenDomain.shift_ofNat]
  simp only [Signing.wordAddress,show 2^5=32 by decide,
    ←BitVec.ofNat_add]
  congr 1
  omega

theorem prelude_children (s : MachineState) (n src : Nat)
    (nBound : n < 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (index : s.getMem 0x81040 = BitVec.ofNat 64 n)
    (source : s.getMem 0x81078 = BitVec.ofNat 64 src)
    (left right : Reference.Digest)
    (children : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress (src+32*n) i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    ∀ i : Fin 4,
      (preludeState s).getMem (Signing.wordAddress 0x80020 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64 := by
  intro i
  have mem := prelude_mem s (Signing.wordAddress 0x80020 i.val)
    n src nBound srcCase index source
  have addr := source_address s n src index source i
  have child := children i
  fin_cases i
  all_goals
    simp (disch := decide) only [if_pos,if_neg] at mem
    simp [Signing.wordAddress] at addr child ⊢
    have linked := mem.trans ((congrArg s.getMem addr).trans child)
    simpa [Signing.wordAddress] using linked

#print axioms prelude_mem
#print axioms prelude_children
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPrelude67
end

/-! The direct67 keygen node header serializes the Merkle query words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenNodeHeader67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem header_mem (s : MachineState) (a : Word) :
    (headerState s).getMem a =
      if a = 0x80018 then s.getMem 0x81018
      else if a = 0x80010 then s.getMem 0x81010
      else if a = 0x80008 then s.getMem 0x81008
      else if a = 0x80000 then (4 : Word) + (s.getMem 0x81000 <<< 8)
      else s.getMem a := by
  simp [headerState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne]

theorem header_words (s : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hchildren : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    ∀ i : Fin 8,
      (headerState s).getMem (Signing.wordAddress 0x80000 i.val) =
        KeygenNode.inputWord level tree left right i := by
  have h0 := hindex 0
  have h1 := hindex 1
  have h2 := hindex 2
  have p0 := hchildren 0
  have p1 := hchildren 1
  have p2 := hchildren 2
  have p3 := hchildren 3
  norm_num [Signing.wordAddress] at h0 h1 h2 p0 p1 p2 p3
  intro i
  fin_cases i <;> simp only [Signing.wordAddress, KeygenNode.inputWord,
    Fin.reduceFinMk, header_mem] <;> norm_num
  · change (4 : Word) + (s.getMem 0x81000 <<< 8) = _
    rw [hlevel]
    change BitVec.ofNat 64 4 + (BitVec.ofNat 64 level <<< 8) = _
    rw [BitVec.shiftLeft_eq_mul_twoPow,
      show BitVec.twoPow 64 8 = BitVec.ofNat 64 (2^8) from by decide,
      ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    norm_num
  · exact h0
  · exact h1
  · exact h2
  · exact p0
  · exact p1
  · exact p2
  · exact p3

#print axioms header_words
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootHeader67


/-! One direct67 keygen H4 query returns the reference parent node. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNode67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev prelude := GroupedBalancedKeygenNodePrelude67.preludeState
private abbrev header := GroupedBalancedKeygenNodeHeader67.headerState

theorem node_answer (hash : Hash) (s : MachineState)
    (n src level tree : Nat) (left right : Reference.Digest)
    (nBound : n < 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (index : s.getMem 0x81040 = BitVec.ofNat 64 n)
    (source : s.getMem 0x81078 = BitVec.ofNat 64 src)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (index0 : s.getMem 0x81040 =
      (BitVec.ofNat 192 tree).extractLsb' 0 64)
    (index1 : s.getMem 0x81010 =
      (BitVec.ofNat 192 tree).extractLsb' 64 64)
    (index2 : s.getMem 0x81018 =
      (BitVec.ofNat 192 tree).extractLsb' 128 64)
    (children : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress (src+32*n) i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    ∀ i : Fin 2,
      (writeHash (header (prelude s))
        (hash (hashInput (header (prelude s))))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (Reference.node hash level tree left right).extractLsb'
          (64*i.val) 64 := by
  have pLevel : (prelude s).getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [GroupedBalancedKeygenNodeControls67.prelude_control s 0x81000
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact levelWord
  have pIndex : ∀ i : Fin 3,
      (prelude s).getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · have h := GroupedBalancedKeygenRootPrelude67.prelude_mem s 0x81008
        n src nBound srcCase index source
      simp (disch := decide) only [if_pos,if_neg] at h
      simpa [prelude,Signing.wordAddress] using h.trans index0
    · have h := GroupedBalancedKeygenNodeControls67.prelude_control s
        0x81010 (by decide) (by decide) (by decide) (by decide) (by decide)
      simpa [prelude,Signing.wordAddress] using h.trans index1
    · have h := GroupedBalancedKeygenNodeControls67.prelude_control s
        0x81018 (by decide) (by decide) (by decide) (by decide) (by decide)
      simpa [prelude,Signing.wordAddress] using h.trans index2
  have pChildren := GroupedBalancedKeygenRootPrelude67.prelude_children
    s n src nBound srcCase index source left right children
  have words := GroupedBalancedKeygenRootHeader67.header_words
    (prelude s) level tree left right pLevel pIndex pChildren
  obtain ⟨_,srcReg,bitsReg,dstReg⟩ :=
    GroupedBalancedKeygenNodeHeader67.header_regs (prelude s)
  exact KeygenNode.node_answer hash (header (prelude s)) level tree
    left right srcReg bitsReg dstReg words

#print axioms node_answer
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNode67
