import SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeHeader67
import SigGolfCandidate.Hypertree.KeygenNode
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeWords67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCoreWords67. -/
section
/-! The verifier node header serializes the canonical 64-byte Merkle query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeHeader67
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

theorem node_query (s : MachineState) (level tree : Nat)
    (left right : Reference.Digest)
    (pc : s.pc = 0x18ac)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hchildren : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    hashInput (headerState s) =
      Reference.packed (KeygenNode.payload level tree left right) := by
  have fields := header_fields s pc
  exact KeygenNode.query_eq (headerState s) level tree left right
    fields.source fields.bits (header_words s level tree left right
      hlevel hindex hchildren)

#print axioms header_mem
#print axioms header_words
#print axioms node_query

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeWords67

end

/-! Functional refinement of the complete Fast2Byte Merkle node body. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCoreWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyWords67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeWords67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem node_core_words (hash : Hash) (s : MachineState)
    (level tree : Nat) (left right : Reference.Digest)
    (pc : s.pc = 0x1880)
    (hlevel : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (hindex : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64)
    (hchildren : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x80520 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64) :
    ∃ final,
      Trace hash image s 80 87 1 1 final ∧
      final.pc = 0x1960 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level tree left right).extractLsb'
            (64*i.val) 64) ∧
      (∀ a : Word,
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80020 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80000 i.val) →
        (∀ i : Fin 4, a ≠ Signing.wordAddress 0x80300 i.val) →
        (∀ i : Fin 2, a ≠ Signing.wordAddress 0x80500 i.val) →
        final.getMem a = s.getMem a) := by
  obtain ⟨copied,first,copiedInv,copiedWords,copiedFrame⟩ :=
    run_copy_words hash s 0x1880 0x520 0x020 4 0x80520 0x80020 4
      child_copy_code.1 child_copy_code.2 pc
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inr (by decide))
  have copiedPC : copied.pc = 0x18ac := by
    have h := copiedInv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  have copiedLevel : copied.getMem 0x81000 = BitVec.ofNat 64 level := by
    rw [copiedFrame 0x81000 (by intro i hi; interval_cases i <;> decide)]
    exact hlevel
  have copiedIndex : ∀ i : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 tree).extractLsb' (64*i.val) 64 := by
    intro i
    have outside : ∀ j, j < 4 →
        Signing.wordAddress 0x81008 i.val ≠
          Signing.wordAddress 0x80020 j := by
      intro j hj
      fin_cases i <;> interval_cases j <;> decide
    rw [copiedFrame _ outside]
    exact hindex i
  have copiedChildren : ∀ i : Fin 4,
      copied.getMem (Signing.wordAddress 0x80020 i.val) =
        if i.val < 2 then left.extractLsb' (64*i.val) 64
        else right.extractLsb' (64*(i.val-2)) 64 := by
    intro i
    rw [copiedWords i.val i.isLt]
    exact hchildren i
  let ready := GroupedBalancedByteFastNodeHeader67.headerState copied
  have headerTrace := GroupedBalancedByteFastNodeHeader67.header_block
    copied copiedPC
  have fields := GroupedBalancedByteFastNodeHeader67.header_fields
    copied copiedPC
  have words := header_words copied level tree left right copiedLevel
    copiedIndex copiedChildren
  have answers := KeygenNode.node_answer hash ready level tree left right
    fields.source fields.bits fields.destination words
  let hashed := writeHash ready (hash (hashInput ready))
  have hashTrace := GroupedBalancedByteFastNodeQuery67.hash_trace
    hash ready fields
  have hashedPC := GroupedBalancedByteFastNodeQuery67.hash_pc
    hash ready fields
  obtain ⟨final,last,lastInv,lastWords,lastFrame⟩ :=
    run_copy_words hash hashed 0x1934 0x300 0x500 2
      0x80300 0x80500 2 result_copy_code.1 result_copy_code.2
      hashedPC
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by simp [setup_reg,signExtend12])
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
  have finalPC : final.pc = 0x1960 := by
    have h := lastInv.2.2.1
    simpa [Keygen.CopyInvariant] using h
  refine ⟨final,?_,finalPC,?_,?_⟩
  · have path := first.trans
      (headerTrace.trace.trans (hashTrace.trans last))
    simpa [image,GroupedBalancedByteFastCopies67.image,
      GroupedBalancedByteFastNodeHeader67.image,
      GroupedBalancedByteFastNodeQuery67.image] using path
  · intro i
    rw [lastWords i.val i.isLt]
    exact answers i
  · intro a childOutside headerOutside hashOutside resultOutside
    have lastOutside : ∀ i, i < 2 →
        a ≠ Signing.wordAddress 0x80500 i := by
      intro i hi
      exact resultOutside ⟨i,hi⟩
    have firstOutside : ∀ i, i < 4 →
        a ≠ Signing.wordAddress 0x80020 i := by
      intro i hi
      exact childOutside ⟨i,hi⟩
    rw [lastFrame a lastOutside,
      Signing.hash_answer_frame ready _ fields.destination a hashOutside]
    rw [header_mem]
    have h18 : a ≠ 0x80018 := by
      simpa [Signing.wordAddress] using headerOutside (3 : Fin 4)
    have h10 : a ≠ 0x80010 := by
      simpa [Signing.wordAddress] using headerOutside (2 : Fin 4)
    have h08 : a ≠ 0x80008 := by
      simpa [Signing.wordAddress] using headerOutside (1 : Fin 4)
    have h00 : a ≠ 0x80000 := by
      simpa [Signing.wordAddress] using headerOutside (0 : Fin 4)
    simp only [if_neg h18, if_neg h10, if_neg h08, if_neg h00]
    exact copiedFrame a firstOutside

#print axioms node_core_words

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeCoreWords67
