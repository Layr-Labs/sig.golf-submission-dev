import SigGolfCandidate.Hypertree.TightCertificate

/-!
The balanced encoding ensures that the 46 verifier chains use at most 161
HASH calls. The exact prefix relation and symbolic bound are proved by the
verifier loop's shared encoding lemmas.
-/

namespace SigGolfCandidate.Hypertree.ChecksumVerifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying KeygenVerifyCount
set_option maxRecDepth 4096

/-- The first 43 remaining chain lengths are exactly the WOTS checksum. -/
theorem chainPrefix_message (message : Reference.Digest) :
    chainPrefix message 43 = Reference.checksum message := by
  change Verifying.chainPrefixFast message 43 = Reference.checksum message
  exact Verifying.chainPrefixFast_message message

theorem chainPrefix_bound_balanced (message : Reference.Digest) :
    chainPrefix message 46 ≤ 161 := by
  change Verifying.chainPrefixFast message 46 ≤ 161
  exact Verifying.chainPrefixFast_bound_balanced message

/-- The checksum prevents all 46 chain lengths from attaining their individual maxima. -/
theorem chainPrefix_bound (message : Reference.Digest) : chainPrefix message 46 ≤ 308 := by
  have bound := chainPrefix_bound_balanced message
  omega

end SigGolfCandidate.Hypertree.ChecksumVerifying
