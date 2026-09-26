import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedIndexStart67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootAt67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomWireSiblings67

/-! The H4 loop starts from the decoded bottom seed's reference leaf root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedStartRoot67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image
private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem start_fields (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial start : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (startRun : Trace hash image initial 218 240 2 3 start) :
    start.getMem 0x81000 = 0 ∧
    GroupedBalancedVerifyTreeHighFrame67.SafeFrame initial start ∧
    GroupedBalancedVerifyStackGlobal67.LowFrame initial start := by
  obtain ⟨otherInitial,otherStart,otherLoaded,otherRun,_,safe,
    _,_,base,low⟩ :=
    GroupedBalancedVerifyTreePrefixSafe67.loaded_tree_start_safe
      hash (message,pk,wire)
  have loadedByte : initialState GroupedBalancedProgram67Byte.submission
      .verify (message,pk,wire) = some initial := by
    rw [GroupedBalancedVerifyH2LoadedSemantic67.initial_verify_eq]
    exact loaded
  have initialEq : otherInitial = initial :=
    Option.some.inj (otherLoaded.symm.trans loadedByte)
  rw [initialEq] at otherRun safe low
  have startEq : otherStart = start := Trace.deterministic otherRun startRun
  rw [startEq] at base safe low
  exact ⟨base,safe,low⟩

theorem start_root (hash : Hash) (message : Message)
    (pk : PublicKey) (wire : Bytes 50848)
    (initial start : MachineState)
    (loaded : initialState program .verify (message,pk,wire) = some initial)
    (pc : initial.pc = 0x1000)
    (startRun : Trace hash image initial 218 240 2 3 start) :
    ∀ i : Fin 2,
      start.getMem (Signing.wordAddress 0x80500 i.val) =
        (GroupedBalancedVerifyBottomRootAt67.rootAt hash
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer)
          (GroupedBalancedWire67.decode wire).bottom 0).extractLsb'
            (64*i.val) 64 := by
  obtain ⟨leaf,leafRun,leafPC,leafWords,_⟩ :=
    GroupedBalancedVerifyH2LoadedSemantic67.loaded_leaf_answer
      hash message pk wire initial loaded pc
  let built := GroupedBalancedVerifyTreeStart67.startState leaf
  have next := GroupedBalancedVerifyTreeStart67.start_steps leaf leafPC
  have builtRun : Trace hash image initial 218 240 2 3 built := by
    simpa only [Nat.reduceAdd] using leafRun.trans next.trace
  have eq : start = built := Trace.deterministic startRun builtRun
  subst start
  intro i
  calc
    built.getMem (Signing.wordAddress 0x80500 i.val) =
        leaf.getMem (Signing.wordAddress 0x80500 i.val) :=
      GroupedBalancedVerifyH4IndexStart67.start_root_frame leaf i
    _ = (GroupedBottomTree.leafFromSeed hash
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer).toNat
          (SignatureEncoding.slice wire 32 16)).extractLsb' (64*i.val) 64 :=
      leafWords i
    _ = (GroupedBalancedVerifyBottomRootAt67.rootAt hash
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer)
          (GroupedBalancedWire67.decode wire).bottom 0).extractLsb'
            (64*i.val) 64 := by
      rw [GroupedBalancedVerifyBottomRootAt67.rootAt_zero,
        GroupedBalancedVerifyBottomWireSiblings67.decoded_seed]

#print axioms start_root
#print axioms start_fields
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedStartRoot67
