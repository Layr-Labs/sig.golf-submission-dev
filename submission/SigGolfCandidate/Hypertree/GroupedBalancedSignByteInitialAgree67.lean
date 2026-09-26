import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign

/-! The original signer code and byte-decoder signer load identical initial
memory and stack. Their first 1086 instructions are also identical. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteInitialAgree67
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem submission_eq : GroupedBalancedProgram67Byte.submission =
    GroupedBalancedProgram67ByteSign.submission := by
  rfl

theorem initial_sign (secretKey : SecretKey) (cache : Cache)
    (message : Message) :
    initialState GroupedBalancedProgram67Byte.submission .sign
      (secretKey,cache,message) =
    initialState GroupedBalancedProgram67ByteSign.submission .sign
      (secretKey,cache,message) := by
  have hdata : GroupedBalancedSignImage67.image.data =
      GroupedBalancedSignImage67Byte.image.data := rfl
  have hbase : Riscv.dataBase GroupedBalancedSignImage67.image =
      Riscv.dataBase GroupedBalancedSignImage67Byte.image := by
    simp only [Riscv.dataBase,hdata]
  simp only [initialState,
    if_pos (GroupedBalancedProgram67Byte.admissible.2 .sign),
    if_pos (GroupedBalancedProgram67ByteSign.admissible.2 .sign)]
  rw [show (GroupedBalancedProgram67Byte.submission.image .sign).data =
      GroupedBalancedSignImage67.image.data from rfl,
    show (GroupedBalancedProgram67ByteSign.submission.image .sign).data =
      GroupedBalancedSignImage67Byte.image.data from rfl,
    show Riscv.dataBase (GroupedBalancedProgram67Byte.submission.image .sign) =
      Riscv.dataBase GroupedBalancedSignImage67.image from rfl,
    show Riscv.dataBase (GroupedBalancedProgram67ByteSign.submission.image .sign) =
      Riscv.dataBase GroupedBalancedSignImage67Byte.image from rfl,
    hdata,hbase]
  rfl

#print axioms initial_sign
#print axioms submission_eq
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteInitialAgree67
