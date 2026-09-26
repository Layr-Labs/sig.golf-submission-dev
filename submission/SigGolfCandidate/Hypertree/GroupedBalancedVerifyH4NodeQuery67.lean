import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Query67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeH4Answer67
import SigGolfCandidate.Hypertree.KeygenNode
import SigGolfCandidate.Hypertree.KeygenDomain
import SigGolfCandidate.Hypertree.SecurityRandomOracle

/-! Serialize a verifier H4 tree-node call from its level, address, and two digests. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4NodeQuery67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private abbrev ready := GroupedBalancedVerifyTreeH4Header67.headerState

theorem header_word (s : MachineState) (i : Fin 4) :
    (ready s).getMem (Signing.wordAddress 0x80000 i.val) =
      if i.val = 0 then 4 + (s.getMem 0x81000 <<< 8)
      else s.getMem (Signing.wordAddress 0x81000 i.val) := by
  fin_cases i <;>
    simp [ready,GroupedBalancedVerifyTreeH4Header67.headerState,
      Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem payload_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
    (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018) :
    (ready s).getMem a = s.getMem a := by
  change a ≠ 524288#64 at h0
  change a ≠ 524296#64 at h1
  change a ≠ 524304#64 at h2
  change a ≠ 524312#64 at h3
  simp [ready,GroupedBalancedVerifyTreeH4Header67.headerState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,h0,h1,h2,h3]

theorem input_words (s : MachineState) (level address : Nat)
    (left right : Reference.Digest)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (addressWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 address).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 8, (ready s).getMem (Signing.wordAddress 0x80000 i.val) =
      KeygenNode.inputWord level address left right i := by
  intro i
  fin_cases i
  · have h := header_word s (0 : Fin 4)
    rw [levelWord] at h
    rw [KeygenDomain.shift_ofNat level 8] at h
    simpa [Signing.wordAddress,KeygenNode.inputWord,BitVec.ofNat_add] using h
  · have h := header_word s (1 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (addressWords 0)
  · have h := header_word s (2 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (addressWords 1)
  · have h := header_word s (3 : Fin 4)
    simpa [Signing.wordAddress,KeygenNode.inputWord] using h.trans (addressWords 2)
  · rw [payload_frame s _ (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using leftWords 0
  · rw [payload_frame s _ (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using leftWords 1
  · rw [payload_frame s _ (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using rightWords 0
  · rw [payload_frame s _ (by decide) (by decide) (by decide) (by decide)]
    simpa [Signing.wordAddress,KeygenNode.inputWord] using rightWords 1

theorem node_query (s : MachineState) (pc : s.pc = 0x13e4)
    (level address : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (addressWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 address).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    hashInput (ready s) = SecurityRandomOracle.addressedInput
      4 level address 0 0 0 (bytes left ++ bytes right) := by
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields s pc
  have input := KeygenNode.query_eq (ready s) level address left right
    fields.source fields.bits
    (input_words s level address left right
      levelWord addressWords leftWords rightWords)
  simpa [KeygenNode.payload,SecurityRandomOracle.addressedInput] using input

theorem node_answer (hash : Hash) (s : MachineState) (pc : s.pc = 0x13e4)
    (level address : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (addressWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 address).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (ready s) (hash (hashInput (ready s)))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (Reference.node hash level address left right).extractLsb'
          (64*i.val) 64 := by
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields s pc
  exact KeygenNode.node_answer hash (ready s) level address left right
    fields.source fields.bits fields.destination
    (input_words s level address left right
      levelWord addressWords leftWords rightWords)

theorem node_copy (hash : Hash) (s : MachineState) (pc : s.pc = 0x13e4)
    (level address : Nat) (left right : Reference.Digest)
    (levelWord : s.getMem 0x81000 = BitVec.ofNat 64 level)
    (addressWords : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 address).extractLsb' (64*i.val) 64)
    (leftWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80020 i.val) =
        left.extractLsb' (64*i.val) 64)
    (rightWords : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80030 i.val) =
        right.extractLsb' (64*i.val) 64) :
    ∃ final,
      OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image
        (writeHash (ready s) (hash (hashInput (ready s)))) 17 final ∧
      final.pc = 0x1498 ∧
      ∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80500 i.val) =
          (Reference.node hash level address left right).extractLsb'
            (64*i.val) 64 := by
  let hashed := writeHash (ready s) (hash (hashInput (ready s)))
  have fields := GroupedBalancedVerifyTreeH4Query67.header_fields s pc
  obtain ⟨final,run,finalPc,words,_,_,_⟩ :=
    GroupedBalancedVerifyTreeH4Answer67.answer_copy hashed
      (GroupedBalancedVerifyTreeH4Query67.hash_pc hash (ready s) fields)
  refine ⟨final,run,finalPc,?_⟩
  intro i
  exact (words i).trans
    (node_answer hash s pc level address left right
      levelWord addressWords leftWords rightWords i)

#print axioms header_word
#print axioms payload_frame
#print axioms input_words
#print axioms node_query
#print axioms node_answer
#print axioms node_copy

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH4NodeQuery67
