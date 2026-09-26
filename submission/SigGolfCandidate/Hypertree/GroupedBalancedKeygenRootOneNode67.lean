import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootNode67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneNode67
import SigGolfCandidate.TraceDeterminism

/-! The actual H4 keygen node stores the reference parent digest. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootOneNode67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image
private abbrev prelude := GroupedBalancedKeygenNodePrelude67.preludeState
private abbrev header := GroupedBalancedKeygenNodeHeader67.headerState
private abbrev hashed (hash : Hash) (s : MachineState) :=
  writeHash (header (prelude s)) (hash (hashInput (header (prelude s))))
private abbrev made (hash : Hash) (s : MachineState) :=
  GroupedBalancedKeygenNodeStore67.storeState (hashed hash s)

theorem hashed_high (hash : Hash) (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) (ne08 : a ≠ 0x81008#64) :
    (hashed hash s).getMem a = s.getMem a := by
  have ne (b : Nat) (below : b < 0x81000) : a ≠ BitVec.ofNat 64 b := by
    intro eq
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b < 2^64)] at hn
    omega
  have p := GroupedBalancedKeygenNodeControls67.prelude_control s a
    ne08 (ne 0x80020 (by decide)) (ne 0x80028 (by decide))
    (ne 0x80030 (by decide)) (ne 0x80038 (by decide))
  have h := GroupedBalancedKeygenNodeControls67.header_control (prelude s) a
    (ne 0x80000 (by decide)) (ne 0x80008 (by decide))
    (ne 0x80010 (by decide)) (ne 0x80018 (by decide))
  have regs := GroupedBalancedKeygenNodeHeader67.header_regs (prelude s)
  have w := GroupedBalancedKeygenNodeControls67.hash_control hash
    (header (prelude s)) a regs.2.2.2 high
  exact w.trans (h.trans p)

theorem concrete_trace (hash : Hash) (s : MachineState) (n src dst : Nat)
    (pc : s.pc = 0x1480) (nBound : n < 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040 = BitVec.ofNat 64 n)
    (source : s.getMem 0x81078 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080 = BitVec.ofNat 64 dst) :
    Trace hash image s 79 86 1 1 (made hash s) := by
  have srcSafe := GroupedBalancedKeygenNodeAddress67.source_accesses s n src
    nBound srcCase index source
  have first : Trace hash image s 21 21 0 0 (prelude s) :=
    (GroupedBalancedKeygenNodePrelude67.prelude_steps s pc
      (by simpa using srcSafe ⟨0,by decide⟩)
      (by simpa using srcSafe ⟨1,by decide⟩)
      (by simpa using srcSafe ⟨2,by decide⟩)
      (by simpa using srcSafe ⟨3,by decide⟩)).trace
  have ppc := GroupedBalancedKeygenNodePrelude67.prelude_pc s pc
  have second : Trace hash image (prelude s) 33 33 0 0 (header (prelude s)) :=
    (GroupedBalancedKeygenNodeHeader67.header_steps (prelude s) ppc).trace
  have hpc := GroupedBalancedKeygenNodeHeader67.header_pc (prelude s) ppc
  have hregs := GroupedBalancedKeygenNodeHeader67.header_regs (prelude s)
  have third : Trace hash image (header (prelude s)) 1 8 1 1 (hashed hash s) :=
    GroupedBalancedKeygenNodeHash67.hash_trace hash (header (prelude s)) hpc hregs
  obtain ⟨other,otherTrace,_,highFrame⟩ :=
    GroupedBalancedKeygenNodeHash67.prelude_header_hash hash s pc
      (by simpa using srcSafe ⟨0,by decide⟩)
      (by simpa using srcSafe ⟨1,by decide⟩)
      (by simpa using srcSafe ⟨2,by decide⟩)
      (by simpa using srcSafe ⟨3,by decide⟩)
  have prefixTrace : Trace hash image s 55 62 1 1 (hashed hash s) := by
    simpa only [Nat.reduceAdd] using (first.trans second).trans third
  have same : other = hashed hash s := Trace.deterministic otherTrace prefixTrace
  subst other
  have hi (a : Word) (high : 0x81000 ≤ a.toNat) (ne08 : a ≠ 0x81008#64) :
      (hashed hash s).getMem a = s.getMem a := highFrame a high ne08
  have hashedIndex : (hashed hash s).getMem 0x81040 = BitVec.ofNat 64 n := by
    rw [hi 0x81040 (by decide) (by decide),index]
  have hashedDestination : (hashed hash s).getMem 0x81080 = BitVec.ofNat 64 dst := by
    rw [hi 0x81080 (by decide) (by decide),destination]
  obtain ⟨destSafe,destNextSafe⟩ :=
    GroupedBalancedKeygenNodeAddress67.destination_accesses (hashed hash s) n dst
      nBound dstCase hashedIndex hashedDestination
  have stored : Trace hash image (hashed hash s) 24 24 0 0 (made hash s) :=
    (GroupedBalancedKeygenNodeStore67.store_steps (hashed hash s)
      (by change (header (prelude s)).pc+4=0x155c; rw [hpc]; decide)
      destSafe destNextSafe).trace
  simpa only [Nat.reduceAdd] using prefixTrace.trans stored

theorem store_word (hashed : MachineState) (n dst : Nat)
    (nBound : n < 8) (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : hashed.getMem 0x81040 = BitVec.ofNat 64 n)
    (destination : hashed.getMem 0x81080 = BitVec.ofNat 64 dst)
    (i : Fin 2) :
    (GroupedBalancedKeygenNodeStore67.storeState hashed).getMem
      (Signing.wordAddress (dst+16*n) i.val) =
      hashed.getMem (Signing.wordAddress 0x80300 i.val) := by
  have addr : (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 =
      BitVec.ofNat 64 (dst+16*n) := by
    have lit40 : (0x81040#64 : Word) = (0x81040 : Word) := by decide
    have lit80 : (0x81080#64 : Word) = (0x81080 : Word) := by decide
    rw [lit40,lit80]
    rw [index,destination,KeygenDomain.shift_ofNat]
    simp [BitVec.ofNat_add,Nat.mul_comm,BitVec.add_comm]
  have range0 : dst+16*n < 2^64 := by rcases dstCase with rfl | rfl <;> omega
  have range1 : dst+16*n+8 < 2^64 := by rcases dstCase with rfl | rfl <;> omega
  have baseNat : ((hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64).toNat =
      dst+16*n := by
    rw [addr]
    simp [BitVec.toNat_ofNat]
    omega
  have nextNat : ((hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 + 8#64).toNat =
      dst+16*n+8 := by
    rw [addr,←BitVec.ofNat_add]
    simp [BitVec.toNat_ofNat]
    omega
  have neCounter0 : (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 ≠ 0x81040#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq
    have val : (0x81040#64 : Word).toNat=0x81040 := by decide
    rw [baseNat,val] at hn
    rcases dstCase with rfl | rfl <;> omega
  have neCounter1 : (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 + 8#64 ≠ 0x81040#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq
    have val : (0x81040#64 : Word).toNat=0x81040 := by decide
    rw [nextNat,val] at hn
    rcases dstCase with rfl | rfl <;> omega
  have distinct : (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 ≠
      (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 + 8#64 := by
    intro eq; have hn := congrArg BitVec.toNat eq
    rw [baseNat,nextNat] at hn
    omega
  fin_cases i
  · have word : Signing.wordAddress (dst+16*n) 0 =
        (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 := by
      simpa [Signing.wordAddress] using addr.symm
    rw [word,GroupedBalancedKeygenNodeStore67.store_mem,
      if_neg neCounter0,if_neg distinct,if_pos rfl]
    rfl
  · have word : Signing.wordAddress (dst+16*n) 1 =
        (hashed.getMem 0x81040#64 <<< 4) + hashed.getMem 0x81080#64 + 8#64 := by
      rw [addr]
      simp [Signing.wordAddress,BitVec.ofNat_add]
    rw [word,GroupedBalancedKeygenNodeStore67.store_mem,
      if_neg neCounter1,if_pos rfl]
    rfl

theorem one_node_values (hash : Hash) (s : MachineState)
    (n k src dst level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x1480) (nBound : n < k) (kBound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
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
    ∃ final,
      Trace hash image s 79 86 1 1 final ∧
      final.pc = (if n+1 = k then 0x15bc else 0x1480) ∧
      final.getMem 0x81040#64 = BitVec.ofNat 64 (n+1) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → a.toNat < 0x82000 →
        a ≠ 0x81008#64 → a ≠ 0x81040#64 → final.getMem a = s.getMem a) ∧
      (∀ i : Fin 2, final.getMem (Signing.wordAddress (dst+16*n) i.val) =
        (Reference.node hash level tree left right).extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0x82000 ≤ a.toNat →
        a ≠ Signing.wordAddress (dst+16*n) 0 →
        a ≠ Signing.wordAddress (dst+16*n) 1 →
        final.getMem a = s.getMem a) := by
  obtain ⟨final,trace,finalPC,finalIndex,lowFrame⟩ :=
    GroupedBalancedKeygenOneNode67.one_node hash s n k src dst pc nBound
      kBound srcCase dstCase index count source destination
  have madeTrace := concrete_trace hash s n src dst pc (by omega)
    srcCase dstCase index source destination
  have same : final = made hash s := Trace.deterministic trace madeTrace
  have hiIndex : (hashed hash s).getMem 0x81040#64 = BitVec.ofNat 64 n := by
    rw [hashed_high hash s 0x81040#64 (by decide) (by decide),index]
  have hiDst : (hashed hash s).getMem 0x81080#64 = BitVec.ofNat 64 dst := by
    rw [hashed_high hash s 0x81080#64 (by decide) (by decide),destination]
  have output := GroupedBalancedKeygenRootNode67.node_answer hash s n src level tree
    left right (by omega) srcCase index source levelWord index0 index1 index2 children
  refine ⟨final,trace,finalPC,finalIndex,lowFrame,?_,?_⟩
  · intro i
    rw [same]
    exact (store_word (hashed hash s) n dst (by omega) dstCase
      hiIndex hiDst i).trans (output i)
  · intro a high ne0 ne1
    rw [same,GroupedBalancedKeygenNodeStore67.store_mem]
    have neCounter : a ≠ 0x81040#64 := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have val : (0x81040#64 : Word).toNat = 0x81040 := by decide
      rw [val] at hn
      omega
    have addr : (hashed hash s).getMem 0x81040#64 <<< 4 +
        (hashed hash s).getMem 0x81080#64 = BitVec.ofNat 64 (dst+16*n) := by
      rw [hiIndex,hiDst,KeygenDomain.shift_ofNat]
      simp [BitVec.ofNat_add,Nat.mul_comm,BitVec.add_comm]
    have baseWord : Signing.wordAddress (dst+16*n) 0 =
        (hashed hash s).getMem 0x81040#64 <<< 4 +
          (hashed hash s).getMem 0x81080#64 := by
      simpa [Signing.wordAddress] using addr.symm
    have nextWord : Signing.wordAddress (dst+16*n) 1 =
        (hashed hash s).getMem 0x81040#64 <<< 4 +
          (hashed hash s).getMem 0x81080#64 + 8#64 := by
      rw [addr]
      simp [Signing.wordAddress,BitVec.ofNat_add]
    rw [if_neg neCounter,if_neg (by simpa only [nextWord] using ne1),
      if_neg (by simpa only [baseWord] using ne0)]
    exact hashed_high hash s a (by omega) (by
      intro eq
      have hn := congrArg BitVec.toNat eq
      have val : (0x81008#64 : Word).toNat = 0x81008 := by decide
      rw [val] at hn
      omega)

#print axioms one_node_values

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootOneNode67
