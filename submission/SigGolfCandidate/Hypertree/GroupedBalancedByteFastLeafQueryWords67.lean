import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeaf67
import SigGolfCandidate.Hypertree.GroupedBalancedByteFastChainEndpoints67
import SigGolfCandidate.Hypertree.KeygenLeafQuery
import Mathlib.Data.List.OfFn


/-! Memory layout prepared for the direct67 upper-leaf hash query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafMemory67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEndpointAccum67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem prelude_mem (s : MachineState) (a : Word) :
    (preludeState s).getMem a =
      if a = 0x80018 then s.getMem 0x81018
      else if a = 0x80010 then s.getMem 0x81010
      else if a = 0x80008 then s.getMem 0x81008
      else if a = 0x80000 then (3 : Word) + (s.getMem 0x81000 <<< 8)
      else if a = 0x81048 then s.getReg .x22
      else s.getMem a := by
  simp [preludeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

#print axioms prelude_mem

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafMemory67


/-! Serialization of the 67 recovered 128-bit WOTS endpoints into the
1,104-byte upper-leaf hash input. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQueryWords67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.Signing
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

def endpointBytes (values : Fin 67 → Reference.Digest) : List Byte :=
  List.ofFn (fun i : Fin (67*16) =>
    (values ⟨i.val/16,by have := i.isLt; omega⟩).extractLsb'
      (8*(i.val%16)) 8)

theorem endpoints_eq (values : Fin 67 → Reference.Digest) :
    ((List.ofFn values).flatMap fun value => bytes value) =
      endpointBytes values := by
  unfold endpointBytes
  rw [List.ofFn_mul (m:=67) (n:=16)]
  simp only [List.flatMap,List.map_ofFn,KeygenLeaf.bytes_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have div : (i.val*16+j.val)/16 = i.val := by omega
  have mod : (i.val*16+j.val)%16 = j.val := by omega
  simp only [div,mod]

def payload (head : Word) (tree : Nat)
    (values : Fin 67 → Reference.Digest) : List Byte :=
  bytes (n:=8) head ++ bytes (n:=24) (BitVec.ofNat 192 tree) ++
    endpointBytes values

@[simp] theorem payload_length (head : Word) (tree : Nat)
    (values : Fin 67 → Reference.Digest) :
    (payload head tree values).length = 1104 := by
  simp only [payload,List.length_append,bytes,List.length_map,
    List.length_range,endpointBytes,List.length_ofFn]

def inputWord (head : Word) (tree : Nat)
    (values : Fin 67 → Reference.Digest) (i : Fin 138) : Word :=
  if i.val=0 then head else if i.val<4 then
    (BitVec.ofNat 192 tree).extractLsb' (64*(i.val-1)) 64 else
    (values ⟨(i.val-4)/2,by have := i.isLt; omega⟩).extractLsb'
      (64*((i.val-4)%2)) 64

theorem payload_byte (head : Word) (tree : Nat)
    (values : Fin 67 → Reference.Digest) (i : Fin 1104) :
    extractByte (inputWord head tree values
      ⟨i.val/8,by have := i.isLt; omega⟩) (i.val%8) =
      (payload head tree values)[i.val]'(by simp) := by
  by_cases first : i.val < 32
  · obtain ⟨i,hi⟩ := i
    dsimp at first
    interval_cases i <;> simp [inputWord,payload,bytes]
    all_goals
      ext j hj
      interval_cases j <;> simp [extractByte,
        ← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat]
  · have big : 32 ≤ i.val := by omega
    have q0 : ¬ i.val/8=0 := by omega
    have q4 : ¬ i.val/8<4 := by omega
    have offset : i.val-32 < 1072 := by have := i.isLt; omega
    have div : (i.val/8-4)/2 = (i.val-32)/16 := by omega
    have shift : 64*((i.val/8-4)%2) + (i.val%8*8) =
        8*((i.val-32)%16) := by omega
    simp only [inputWord,q0,q4,↓reduceIte,payload,List.getElem_append,
      bytes,List.length_map,List.length_range,List.length_append]
    simp only [show ¬ i.val<8+24 from by omega,↓reduceDIte,
      endpointBytes,List.getElem_ofFn]
    simp only [div]
    ext j hj
    have low : i.val%8*8+j < 64 := by omega
    simp [extractByte,low,← Nat.add_assoc,shift]

theorem query_eq (s : MachineState) (head : Word) (tree : Nat)
    (values : Fin 67 → Reference.Digest)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 8832)
    (words : ∀ i : Fin 138,
      s.getMem (wordAddress 0x80000 i.val) =
        inputWord head tree values i) :
    hashInput s = Reference.packed (payload head tree values) := by
  apply Serialization.hashInput_of_list s 0x80000
    (payload head tree values)
  · exact source
  · rw [bits,payload_length]; rfl
  · intro i hi
    have bound : i < 1104 := by simpa using hi
    rw [Signing.getByte_word s 0x80000 i (by decide) (by omega),
      words ⟨i/8,by omega⟩]
    exact payload_byte head tree values ⟨i,bound⟩

theorem leaf_hash_eq (hash : Hash) (s : MachineState)
    (base leaf : Nat) (values : Fin 67 → Reference.Digest)
    (source : s.getReg .x10 = 0x80000)
    (bits : s.getReg .x11 = 8832)
    (words : ∀ i : Fin 138,
      s.getMem (wordAddress 0x80000 i.val) =
        inputWord (KeygenDomain.header 3 base 0 0 0) leaf values i) :
    Reference.truncate (hash (hashInput s)) =
      GroupedBalancedUpperTree67.compressLeaf hash base leaf values := by
  rw [query_eq s _ leaf values source bits words]
  simp only [GroupedBalancedUpperTree67.compressLeaf,Reference.query,
    KeygenDomain.header,payload]
  rw [endpoints_eq]

#print axioms leaf_hash_eq

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafQueryWords67
