import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneNode67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootPriorLeavesFrame67

/-! The H4 parent-node trace does not touch the public cache area. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheNode67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

def CacheFrame (s t : MachineState) : Prop :=
  ∀ a : Word, a.toNat < 0x20060 → t.getMem a = s.getMem a

theorem CacheFrame.refl (s : MachineState) : CacheFrame s s := by
  intro _ _
  rfl

theorem CacheFrame.trans {s t u : MachineState}
    (first : CacheFrame s t) (second : CacheFrame t u) :
    CacheFrame s u := by
  intro a low
  rw [second a low,first a low]

private theorem ne_high (a : Word) (low : a.toNat < 0x20060)
    (b : Nat) (lower : 0x80000 ≤ b) (upper : b < 2^64) :
    a ≠ BitVec.ofNat 64 b := by
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt upper] at h
  omega

theorem hash_prelude_cache (hash : Hash) (s final : MachineState)
    (pc : s.pc = 0x1480)
    (safe0 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64) 8 = true)
    (safe1 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 8#64) 8 = true)
    (safe2 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 16#64) 8 = true)
    (safe3 : accessValid ((s.getMem 0x81040#64 <<< 5) + s.getMem 0x81078#64 + 24#64) 8 = true)
    (trace : Trace hash image s 55 62 1 1 final) :
    CacheFrame s final := by
  let prepared := GroupedBalancedKeygenNodePrelude67.preludeState s
  have first : Trace hash image s 21 21 0 0 prepared :=
    (GroupedBalancedKeygenNodePrelude67.prelude_steps s pc
      safe0 safe1 safe2 safe3).trace
  have preparedPC := GroupedBalancedKeygenNodePrelude67.prelude_pc s pc
  let ready := GroupedBalancedKeygenNodeHeader67.headerState prepared
  have second : Trace hash image prepared 33 33 0 0 ready :=
    (GroupedBalancedKeygenNodeHeader67.header_steps prepared preparedPC).trace
  have readyPC := GroupedBalancedKeygenNodeHeader67.header_pc prepared preparedPC
  have readyRegs := GroupedBalancedKeygenNodeHeader67.header_regs prepared
  let made := writeHash ready (hash (hashInput ready))
  have third : Trace hash image ready 1 8 1 1 made :=
    GroupedBalancedKeygenNodeHash67.hash_trace hash ready readyPC readyRegs
  have total : Trace hash image s 55 62 1 1 made := by
    simpa only [Nat.reduceAdd] using (first.trans second).trans third
  have same : final = made := Trace.deterministic trace total
  rw [same]
  intro a low
  have before : prepared.getMem a = s.getMem a :=
    GroupedBalancedKeygenNodeControls67.prelude_control s a
      (ne_high a low 0x81008 (by decide) (by decide))
      (ne_high a low 0x80020 (by decide) (by decide))
      (ne_high a low 0x80028 (by decide) (by decide))
      (ne_high a low 0x80030 (by decide) (by decide))
      (ne_high a low 0x80038 (by decide) (by decide))
  have header : ready.getMem a = prepared.getMem a :=
    GroupedBalancedKeygenNodeControls67.header_control prepared a
      (ne_high a low 0x80000 (by decide) (by decide))
      (ne_high a low 0x80008 (by decide) (by decide))
      (ne_high a low 0x80010 (by decide) (by decide))
      (ne_high a low 0x80018 (by decide) (by decide))
  have answer : made.getMem a = ready.getMem a := by
    apply Signing.hash_answer_frame ready (hash (hashInput ready))
      readyRegs.2.2.2
    intro i sameWord
    have h := congrArg BitVec.toNat sameWord
    simp only [Signing.wordAddress,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := i.isLt; omega)] at h
    omega
  exact answer.trans (header.trans before)

theorem one_node_cache (hash : Hash) (s final : MachineState)
    (n k src dst : Nat)
    (pc : s.pc = 0x1480) (nBound : n < k) (kBound : k ≤ 8)
    (srcCase : src = 0x82000 ∨ src = 0x82100)
    (dstCase : dst = 0x82000 ∨ dst = 0x82100)
    (index : s.getMem 0x81040#64 = BitVec.ofNat 64 n)
    (count : s.getMem 0x81070#64 = BitVec.ofNat 64 k)
    (source : s.getMem 0x81078#64 = BitVec.ofNat 64 src)
    (destination : s.getMem 0x81080#64 = BitVec.ofNat 64 dst)
    (trace : Trace hash image s 79 86 1 1 final) :
    CacheFrame s final := by
  have srcSafe := GroupedBalancedKeygenNodeAddress67.source_accesses s n src
    (by omega) srcCase index source
  obtain ⟨hashed,first,hashedPC,hashedFrame⟩ :=
    GroupedBalancedKeygenNodeHash67.prelude_header_hash hash s pc
      (by simpa using srcSafe ⟨0,by decide⟩)
      (by simpa using srcSafe ⟨1,by decide⟩)
      (by simpa using srcSafe ⟨2,by decide⟩)
      (by simpa using srcSafe ⟨3,by decide⟩)
  have firstFrame := hash_prelude_cache hash s hashed pc
    (by simpa using srcSafe ⟨0,by decide⟩)
    (by simpa using srcSafe ⟨1,by decide⟩)
    (by simpa using srcSafe ⟨2,by decide⟩)
    (by simpa using srcSafe ⟨3,by decide⟩) first
  have hashedIndex : hashed.getMem 0x81040#64 = BitVec.ofNat 64 n := by
    rw [hashedFrame 0x81040#64 (by decide) (by decide),index]
  have hashedDestination : hashed.getMem 0x81080#64 = BitVec.ofNat 64 dst := by
    rw [hashedFrame 0x81080#64 (by decide) (by decide),destination]
  obtain ⟨destLow,destNextLow⟩ :=
    GroupedBalancedKeygenNodeAddress67.destination_low hashed n dst
      (by omega) dstCase hashedIndex hashedDestination
  obtain ⟨destSafe,destNextSafe⟩ :=
    GroupedBalancedKeygenNodeAddress67.destination_accesses hashed n dst
      (by omega) dstCase hashedIndex hashedDestination
  let made := GroupedBalancedKeygenNodeStore67.storeState hashed
  have second : Trace hash image hashed 24 24 0 0 made :=
    (GroupedBalancedKeygenNodeStore67.store_steps hashed hashedPC
      destSafe destNextSafe).trace
  have total : Trace hash image s 79 86 1 1 made := by
    simpa only [Nat.reduceAdd] using first.trans second
  have same : final = made := Trace.deterministic trace total
  rw [same]
  intro a low
  have store : made.getMem a = hashed.getMem a :=
    GroupedBalancedKeygenNodeStore67.store_below_frame hashed a
      (by omega)
      (ne_high a low 0x81040 (by decide) (by decide))
      destLow destNextLow
  exact store.trans (firstFrame a low)

#print axioms hash_prelude_cache
#print axioms one_node_cache

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootCacheNode67
