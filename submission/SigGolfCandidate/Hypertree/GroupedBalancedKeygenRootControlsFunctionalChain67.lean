import SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsAfterSeed67
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSeed67

/-! Functional H1 inputs imply the two tree-address control words survive a full WOTS chain. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFunctionalChain67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedKeygenRootControlsTick67
open GroupedBalancedKeygenRootControlsAfterSeed67
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedKeygenImage67.image

private theorem control_of_words (s ready : MachineState)
    (frame : ∀ i : Fin 2,
      ready.getMem (Signing.wordAddress 0x81010 i.val) =
        s.getMem (Signing.wordAddress 0x81010 i.val)) :
    ControlFrame s ready := by
  constructor
  · simpa [Signing.wordAddress]
      using frame ⟨0,by decide⟩
  · simpa [Signing.wordAddress]
      using frame ⟨1,by decide⟩

theorem regular_even_control (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf k : Nat) (bound : k < 33)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 (2*k))
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s 213 241 4 4 final) :
    ControlFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_,_,_,control,_⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf k (by omega) pc counter level address secret
  exact regular_after_seed hash s ready final (2*k) 127 134 1 1
    (by omega) seedTrace (control_of_words s ready control)
    readyPC readyCounter readyIndex
    (by simpa only [Nat.reduceAdd] using trace)

theorem regular_odd_control (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf n : Nat) (bound : n < 65)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = BitVec.ofNat 64 n)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (n/2)).extractLsb'
          (128+64*i.val) 64)
    (trace : Trace hash image s 112 133 3 3 final) :
    ControlFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_,_,_,control,_⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf n pc (by omega) counter odd cached
  exact regular_after_seed hash s ready final n 26 26 0 0
    bound seedTrace (control_of_words s ready control)
    readyPC readyCounter readyIndex
    (by simpa only [Nat.reduceAdd] using trace)

theorem special65_control (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 65#64)
    (odd : s.getMem 0x81030 &&& 1 ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val) =
        (GroupedBalancedUpperTree67.secretPair hash secretKey 156 leaf (65/2)).extractLsb'
          (128+64*i.val) 64)
    (trace : Trace hash image s 131 187 8 8 final) :
    ControlFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_,_,_,control,_⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.odd_seed_h1
      hash secretKey s leaf 65 pc (by decide) counter odd cached
  exact special65_after_seed hash s ready final 26 26 0 0
    seedTrace (control_of_words s ready control)
    readyPC readyCounter readyIndex
    (by simpa only [Nat.reduceAdd] using trace)

theorem special66_control (hash : Hash) (secretKey : SecretKey)
    (s final : MachineState) (leaf : Nat)
    (pc : s.pc = 0x1050)
    (counter : s.getMem 0x81030 = 66#64)
    (level : s.getMem 0x81000 = 156)
    (address : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (secret : ∀ i : Fin 4,
      s.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64)
    (trace : Trace hash image s 241 318 11 11 final) :
    ControlFrame s final := by
  obtain ⟨ready,seedTrace,readyPC,readyIndex,readyCounter,_,_,_,_,control,_⟩ :=
    GroupedBalancedKeygenLeafFunctionalSeed67.even_seed_h1
      hash secretKey s leaf 33 (by decide) pc (by simpa using counter)
      level address secret
  exact special66_after_seed hash s ready final 127 134 1 1
    seedTrace (control_of_words s ready control)
    readyPC (by simpa using readyCounter) (by simpa using readyIndex)
    (by simpa only [Nat.reduceAdd] using trace)

#print axioms regular_even_control
#print axioms regular_odd_control
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenRootControlsFunctionalChain67
