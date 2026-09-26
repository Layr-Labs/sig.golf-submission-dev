import SigGolfCandidate.Hypertree.GroupedBalancedQuaternary

/-! A direct 67-chain decoder using a two-byte digit-sum table. All table
entries are defined by transparent arithmetic; no SAT oracle is needed. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def code : List (BitVec 32) := [
  0x00080537, 0x50050513, 0x000805b7, 0x60058593, 0x00050313, 0x00000713, 0x01000913, 0x00010893,
  0x00034983, 0x01388a33, 0x000a4a03, 0x01470733, 0x00130313, 0xfff90913, 0xfe0914e3, 0x06073813,
  0x00080863, 0x04058023, 0x00370b93, 0x0140006f, 0x00300c13, 0x05858023, 0x0c000b93, 0x40eb8bb3,
  0x10010893, 0x00a81a13, 0x014888b3, 0x01000913, 0x00054983, 0x00299a13, 0x01488ab3, 0x000aab03,
  0x0165a023, 0x00150513, 0x00458593, 0xfff90913, 0xfe0910e3, 0x00900c93, 0x039bfd33, 0x039bddb3,
  0x01a580a3, 0x01b58123, 0x00000293, 0x00100513, 0x00000073
]

def byteSum (value : Nat) : Nat :=
  ∑ k : Fin 4, value / 4 ^ k.val % 4

def rawByteDigit (entry j : Nat) : Nat := entry / 4 ^ j % 4

/-- The first 256 bytes contain four-digit sums. Two 1 KiB digit tables
follow, in little-endian four-byte entries. -/
def dataByte (i : Fin 2304) : BitVec 8 :=
  if i.val < 256 then
    BitVec.ofNat 8 (byteSum i.val)
  else if i.val < 1280 then
    BitVec.ofNat 8 (rawByteDigit ((i.val - 256) / 4) ((i.val - 256) % 4))
  else
    BitVec.ofNat 8 (3 - rawByteDigit ((i.val - 1280) / 4) ((i.val - 1280) % 4))

def data : List (BitVec 8) := List.ofFn dataByte

def image : Riscv.Image where
  code := code
  data := data

theorem code_length : code.length = 45 := by decide

theorem data_length : data.length = 2304 := by
  simp only [data, List.length_ofFn]

theorem image_bytes : 4 * code.length + data.length = 2484 := by
  rw [code_length, data_length]

theorem data_base : Riscv.dataBase image = 0xfff700 := by
  simp only [Riscv.dataBase, image, data_length, SigGolf.MEMORY_BYTES]
  decide

theorem pair_table_byte (entry : Fin 256) :
    data[entry.val]'(by rw [data_length]; omega) =
      BitVec.ofNat 8 (byteSum entry.val) := by
  simp only [data, List.getElem_ofFn, dataByte, if_pos entry.isLt]

theorem plain_table_byte (entry : Fin 256) (j : Fin 4) :
    data[256 + 4 * entry.val + j.val]'(by rw [data_length]; omega) =
      BitVec.ofNat 8 (rawByteDigit entry.val j.val) := by
  have hlow : ¬256 + 4 * entry.val + j.val < 256 := by omega
  have htable : 256 + 4 * entry.val + j.val < 1280 := by omega
  have hsub : 256 + 4 * entry.val + j.val - 256 = 4 * entry.val + j.val := by omega
  have hdiv : (4 * entry.val + j.val) / 4 = entry.val := by omega
  have hmod : (4 * entry.val + j.val) % 4 = j.val := by omega
  simp only [data, List.getElem_ofFn, dataByte, if_neg hlow,
    if_pos htable, hsub, hdiv, hmod]

theorem flipped_table_byte (entry : Fin 256) (j : Fin 4) :
    data[1280 + 4 * entry.val + j.val]'(by rw [data_length]; omega) =
      BitVec.ofNat 8 (3 - rawByteDigit entry.val j.val) := by
  have hlow : ¬1280 + 4 * entry.val + j.val < 256 := by omega
  have htable : ¬1280 + 4 * entry.val + j.val < 1280 := by omega
  have hsub : 1280 + 4 * entry.val + j.val - 1280 = 4 * entry.val + j.val := by omega
  have hdiv : (4 * entry.val + j.val) / 4 = entry.val := by omega
  have hmod : (4 * entry.val + j.val) % 4 = j.val := by omega
  simp only [data, List.getElem_ofFn, dataByte, if_neg hlow,
    if_neg htable, hsub, hdiv, hmod]

theorem all_words_decode :
    ∀ i : Fin 45, Riscv.decodeInstruction
      (code[i.val]'(by rw [code_length]; exact i.isLt)) ≠ none := by
  intro i
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
