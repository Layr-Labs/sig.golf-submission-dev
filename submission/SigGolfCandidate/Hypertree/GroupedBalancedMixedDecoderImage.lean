import SigGolf
namespace SigGolfCandidate.Hypertree.GroupedBalancedMixedDecoderImage
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def code : List (BitVec 32) := [
  0x00080537, 0x50050513, 0x000805b7, 0x60058593, 0x00053283, 0x00853303, 0x00013383, 0x00813403,
  0x01013483, 0x0022d613, 0x00767633, 0x0072f6b3, 0x00d60633, 0x00465693, 0x0086f6b3, 0x00867633,
  0x00d60633, 0x02960633, 0x03865713, 0x00235613, 0x00767633, 0x007376b3, 0x00d60633, 0x00465693,
  0x0086f6b3, 0x00867633, 0x00d60633, 0x02960633, 0x03865793, 0x00f70733, 0x06073813, 0x00080863,
  0x04058023, 0x00370b93, 0x0140006f, 0x00300c13, 0x05858023, 0x0c000b93, 0x40eb8bb3, 0x02010893,
  0x00a81a13, 0x014888b3, 0x01000913, 0x00054983, 0x00299a13, 0x01488ab3, 0x000aab03, 0x0165a023,
  0x00150513, 0x00458593, 0xfff90913, 0xfe0910e3, 0x003bfc13, 0x018580a3, 0x002bdc13, 0x00500c93,
  0x039c7d33, 0x039c5db3, 0x01a58123, 0x01b581a3, 0x00000293, 0x00100513, 0x00000073
]

/-- Base-four digit `j` of a source byte. -/
def rawByteDigit (entry j : Nat) : Nat := entry / 4 ^ j % 4

/-- Exact two-table byte layout emitted by the standalone assembler. -/
def dataByte (i : Fin 2080) : BitVec 8 :=
  if i.val < 24 then
    let word := if i.val / 8 = 0 then 0x3333333333333333
      else if i.val / 8 = 1 then 0x0f0f0f0f0f0f0f0f
      else 0x0101010101010101
    BitVec.ofNat 8 (word / 2 ^ (8 * (i.val % 8)) % 256)
  else if i.val < 32 then 0
  else if i.val < 1056 then
    BitVec.ofNat 8 (rawByteDigit ((i.val - 32) / 4) ((i.val - 32) % 4))
  else
    BitVec.ofNat 8 (3 - rawByteDigit ((i.val - 1056) / 4) ((i.val - 1056) % 4))

def data : List (BitVec 8) := List.ofFn dataByte

theorem data_length : data.length = 2080 := by simp only [data, List.length_ofFn]

theorem plain_table_byte (entry : Fin 256) (j : Fin 4) :
    data[32 + 4 * entry.val + j.val]'(by rw [data_length]; omega) =
      BitVec.ofNat 8 (rawByteDigit entry.val j.val) := by
  have hlow : ¬32 + 4 * entry.val + j.val < 24 := by omega
  have hpad : ¬32 + 4 * entry.val + j.val < 32 := by omega
  have htable : 32 + 4 * entry.val + j.val < 1056 := by omega
  have hsub : 32 + 4 * entry.val + j.val - 32 = 4 * entry.val + j.val := by omega
  have hdiv : (4 * entry.val + j.val) / 4 = entry.val := by omega
  have hmod : (4 * entry.val + j.val) % 4 = j.val := by omega
  simp only [data, List.getElem_ofFn, dataByte, if_neg hlow, if_neg hpad,
    if_pos htable, hsub, hdiv, hmod]

theorem flipped_table_byte (entry : Fin 256) (j : Fin 4) :
    data[1056 + 4 * entry.val + j.val]'(by rw [data_length]; omega) =
      BitVec.ofNat 8 (3 - rawByteDigit entry.val j.val) := by
  have hlow : ¬1056 + 4 * entry.val + j.val < 24 := by omega
  have hpad : ¬1056 + 4 * entry.val + j.val < 32 := by omega
  have htable : ¬1056 + 4 * entry.val + j.val < 1056 := by omega
  have hsub : 1056 + 4 * entry.val + j.val - 1056 = 4 * entry.val + j.val := by omega
  have hdiv : (4 * entry.val + j.val) / 4 = entry.val := by omega
  have hmod : (4 * entry.val + j.val) % 4 = j.val := by omega
  simp only [data, List.getElem_ofFn, dataByte, if_neg hlow, if_neg hpad,
    if_neg htable, hsub, hdiv, hmod]

def image : Riscv.Image where
  code := code
  data := data

theorem code_length : code.length = 63 := by decide
theorem image_bytes : 4 * code.length + data.length = 2332 := by
  rw [code_length, data_length]

theorem all_words_decode :
    ∀ i : Fin 63, Riscv.decodeInstruction
      (code[i.val]'(by rw [code_length]; exact i.isLt)) ≠ none := by
  intro i
  fin_cases i <;> decide
end SigGolfCandidate.Hypertree.GroupedBalancedMixedDecoderImage
