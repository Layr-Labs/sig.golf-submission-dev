import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalFirst67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenEndpointCopy67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSelector67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalEndpoint67. -/
section
/-! The three selector branches choose the correct direct67 endpoint length. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSelector67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenLeafFunctionalFirst67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem after_selector_value (hash : Hash) (s t : MachineState)
    (ordinary maxStep base tree : Nat)
    (chain : GroupedBalancedChecksum67.Chain)
    (value : Reference.Digest)
    (path : OrdinarySteps image s ordinary t)
    (frame : ∀ a : Word, t.getMem a = s.getMem a)
    (pc : t.pc = 0x12a8)
    (lower : 2 ≤ maxStep) (upper : maxStep ≤ 10)
    (baseBound : base < 256)
    (maxReg : t.getReg .x20 = BitVec.ofNat 64 maxStep)
    (zero : t.getReg .x21 = 0)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s
        (ordinary+(4*maxStep+6))
        (ordinary+(11*maxStep+6)) maxStep maxStep final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            0 maxStep value).extractLsb' (64*i.val) 64) := by
  have tHeader : t.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val 0 := by
    rw [frame]
    exact header
  have tTree : ∀ i : Fin 3,
      t.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame]
    exact treeWords i
  have tValue : ∀ i : Fin 2,
      t.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64 := by
    intro i
    rw [frame]
    exact valueWords i
  obtain ⟨final,tail,done,counter,result⟩ :=
    post_selector_value hash t base tree maxStep chain value pc lower upper
      baseBound maxReg zero tHeader tTree tValue
  refine ⟨final,?_,done,?_,result⟩
  · simpa only [Nat.zero_add] using (path.trace (hash := hash)).trans tail
  · rw [counter,frame]

theorem normal_chain_value (hash : Hash) (s : MachineState)
    (base tree : Nat) (chain : GroupedBalancedChecksum67.Chain)
    (value : Reference.Digest)
    (pc : s.pc = 0x127c)
    (not65 : s.getReg .x19 ≠ 65#64)
    (not66 : s.getReg .x19 ≠ 66#64)
    (baseBound : base < 256)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 chain.val 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 26 47 3 3 final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree chain)
            0 3 value).extractLsb' (64*i.val) 64) := by
  let t := GroupedBalancedKeygenWotsSelector67.selectorState s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.normal_fields s pc not65 not66
  obtain ⟨final,path,done,counter,result⟩ :=
    after_selector_value hash s t 8 3 base tree chain value
      (GroupedBalancedKeygenWotsSelectorAll67.normal_steps s pc not65 not66)
      (GroupedBalancedKeygenWotsSelector67.selector_mem s)
      tpc (by decide) (by decide) baseBound tmax tzero
      header treeWords valueWords
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,counter,result⟩

theorem special65_chain_value (hash : Hash) (s : MachineState)
    (base tree : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 65#64)
    (baseBound : base < 256)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 65 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 45 101 8 8 final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨65,by decide⟩) 0 8 value).extractLsb' (64*i.val) 64) := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special65 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special65_fields s pc index
  have frame (a : Word) : t.getMem a = s.getMem a := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special65,
      execInstrBr,signExtend12,signExtend13,signExtend21]
  obtain ⟨final,path,done,counter,result⟩ :=
    after_selector_value hash s t 7 8 base tree ⟨65,by decide⟩ value
      (GroupedBalancedKeygenWotsSelectorAll67.special65_steps s pc index)
      frame tpc (by decide) (by decide) baseBound tmax tzero
      header treeWords valueWords
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,counter,result⟩

theorem special66_chain_value (hash : Hash) (s : MachineState)
    (base tree : Nat) (value : Reference.Digest)
    (pc : s.pc = 0x127c)
    (index : s.getReg .x19 = 66#64)
    (baseBound : base < 256)
    (header : s.getMem 0x80000 =
      KeygenDomain.header 2 base 0 66 0)
    (treeWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (valueWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∃ final,
      Trace hash image s 54 124 10 10 final ∧
      final.pc = 0x12d0 ∧
      final.getMem 0x81030 = s.getMem 0x81030 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val) =
          (walk (GroupedBalancedUpperTree67.chainHash hash base tree
            ⟨66,by decide⟩) 0 10 value).extractLsb' (64*i.val) 64) := by
  let t := GroupedBalancedKeygenWotsSelectorAll67.special66 s
  obtain ⟨tpc,tmax,tzero,_⟩ :=
    GroupedBalancedKeygenWotsSelectorAll67.special66_fields s pc index
  have frame (a : Word) : t.getMem a = s.getMem a := by
    simp [t,GroupedBalancedKeygenWotsSelectorAll67.special66,
      execInstrBr,signExtend12,signExtend13]
  obtain ⟨final,path,done,counter,result⟩ :=
    after_selector_value hash s t 8 10 base tree ⟨66,by decide⟩ value
      (GroupedBalancedKeygenWotsSelectorAll67.special66_steps s pc index)
      frame tpc (by decide) (by decide) baseBound tmax tzero
      header treeWords valueWords
  exact ⟨final,by simpa only [Nat.reduceMul,Nat.reduceAdd] using path,
    done,counter,result⟩

#print axioms after_selector_value
#print axioms normal_chain_value
#print axioms special65_chain_value
#print axioms special66_chain_value

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSelector67

end

/-! The bytecode endpoint copy places a WOTS digest in the 67-entry leaf table. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalEndpoint67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenEndpointCopy67
open GroupedBalancedKeygenLeafFunctionalSelector67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

theorem copy_endpoint_words (s : MachineState) (n : Nat)
    (bound : n < 67)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (value : Reference.Digest)
    (source : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        value.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (copyState s).getMem
        (Signing.wordAddress 0x80800 (2*n+i.val)) =
          value.extractLsb' (64*i.val) 64 := by
  have base : address s = Signing.wordAddress 0x80800 (2*n) := by
    rw [address_eq s n counter]
    change BitVec.ofNat 64 (0x80800+16*n) =
      BitVec.ofNat 64 (0x80800+8*(2*n))
    congr 1
    omega
  have next : address s + 8 = Signing.wordAddress 0x80800 (2*n+1) := by
    rw [base]
    change BitVec.ofNat 64 (0x80800+8*(2*n)) + BitVec.ofNat 64 8 =
      BitVec.ofNat 64 (0x80800+8*(2*n+1))
    rw [← BitVec.ofNat_add]
    congr 1
  intro i
  fin_cases i
  · change (copyState s).getMem
        (Signing.wordAddress 0x80800 (2*n)) = value.extractLsb' 0 64
    have distinct : Signing.wordAddress 0x80800 (2*n) ≠ 0x81030#64 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat] at h
      omega
    rw [copy_mem]
    have first : Signing.wordAddress 0x80800 (2*n) = address s := base.symm
    have ne : address s ≠ address s + 8 := by
      rw [next,base]
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat] at h
      omega
    split_ifs with h0 hnext
    · exact False.elim (distinct h0)
    · exact False.elim (ne (first.symm.trans hnext))
    · simpa [Signing.wordAddress] using source ⟨0,by decide⟩
  · change (copyState s).getMem
        (Signing.wordAddress 0x80800 (2*n+1)) = value.extractLsb' 64 64
    have distinct : Signing.wordAddress 0x80800 (2*n+1) ≠ 0x81030#64 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [Signing.wordAddress,BitVec.toNat_ofNat] at h
      omega
    rw [copy_mem]
    have second : Signing.wordAddress 0x80800 (2*n+1) = address s + 8 :=
      next.symm
    split_ifs with h0 hnext hbase
    · exact False.elim (distinct h0)
    · simpa [Signing.wordAddress] using source ⟨1,by decide⟩

#print axioms copy_endpoint_words

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalEndpoint67
