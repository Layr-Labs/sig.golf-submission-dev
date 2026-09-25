import SigGolfCandidate.Hypertree.VerifyChainDirect
import SigGolfCandidate.Hypertree.ChainLoopControl

namespace SigGolfCandidate.Hypertree.Verifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem verify_chain_check : ChainLoopControl.CheckCode verify 0x14ec := by decide

theorem verify_chain_increment : ChainLoopControl.IncrementCode verify 0x161c (-332) := by decide

theorem verify_chain_code : VerifyChainDirect.Code verify 0x1500 := VerifyChainDirect.verify_code

end SigGolfCandidate.Hypertree.Verifying
