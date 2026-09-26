import SigGolfCandidate.Hypertree.SignExecutionSetup
import SigGolfCandidate.Hypertree.SignFinish
import SigGolfCandidate.Hypertree.SignWire
import SigGolfCandidate.Hypertree.VerifyFunctional
import SigGolfCandidate.Hypertree.KeygenExpandOrganizer

/-! Inlined from SigGolfCandidate.Hypertree.SignExecution; its only importer was SigGolfCandidate.Hypertree.CandidateHonest. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Actual universal signer execution, with an exact compression count and reference output words.
Signing succeeds for every secret key, cache, and message. -/
theorem sign_execution (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ initial final instructions cycles,
      initialState submission .sign (secretKey,cache,message)=some initial ∧
      Executes hash sign initial instructions ⟨.success,final,cycles,117508,121008⟩ ∧
      instructions≤16072893 ∧ cycles≤16928763 ∧
      LayersStored final 0 (Reference.sign hash secretKey message).layers ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val)=
        (Reference.sign hash secretKey message).randomizer.extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,ready,loaded,pre,readyPC,data,randomizer⟩ := loaded_loop_data hash secretKey cache message
  let index := Reference.indexOf hash message (Reference.randomizer hash secretKey message)
  have small : index.toNat<2^192 := by have := index.isLt; omega
  obtain ⟨done,n,c,body,nb,cb,donePC,_,stored,frame⟩ :=
    sign_layers hash secretKey 160 ready 0 index.toNat 0 (by decide) small (by simpa using readyPC) data
  obtain ⟨final,footer,footerFrame⟩ := sign_footer_executes hash done donePC
  have all := (pre.trans body).then_executes footer
  have execution : Executes hash sign initial (238+n+3) ⟨.success,final,268+c+3,117508,121008⟩ := by
    simpa only [Execution.charge,show loopCalls 160 0=117506 by rfl,show loopBlocks 160 0=121004 by rfl,
      Nat.reduceAdd,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  refine ⟨initial,final,238+n+3,268+c+3,loaded,execution,by omega,by omega,?_,?_⟩
  · have transport : ∀ (level : Nat) (signatures : List Reference.LayerSignature),
        LayersStored done level signatures → LayersStored final level signatures := by
      intro level signatures
      induction signatures generalizing level with
      | nil => intro _; trivial
      | cons signature rest ih =>
        intro h
        refine ⟨?_,ih (level+1) h.2⟩
        have hstored := h.1
        unfold LayerStored at hstored ⊢
        split at hstored <;> rename_i zero
        · rw [if_pos zero]
          exact ⟨fun i => (footerFrame _).trans (hstored.1 i),fun i => (footerFrame _).trans (hstored.2 i)⟩
        · rw [if_neg zero]
          exact ⟨fun chain i => (footerFrame _).trans (hstored.1 chain i),fun i => (footerFrame _).trans (hstored.2 i)⟩
    exact transport 0 _ stored
  · intro i
    rw [footerFrame]
    rw [show wordAddress 0x20060 i.val=BitVec.ofNat 64 (0x20060+8*i.val) by rfl,
      frame _ (by have := i.isLt; omega) (by omega) (by have := i.isLt; change 0x20060+8*i.val<0x20080; omega)]
    exact randomizer i

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_execution
end SigGolfCandidate.Hypertree.Signing
end

/-! Inlined from SigGolfCandidate.Hypertree.SignRun; its only importer was SigGolfCandidate.Hypertree.CandidateHonest. -/
section
namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying SignatureEncoding
set_option maxRecDepth 4096

/-- Exact official signer output for arbitrary secret keys, caches, messages, and oracles. -/
theorem sign_run_refines (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16928763 ∧ submission.runWith hash .sign (secretKey,cache,message)=
      ⟨some ((signCompact hash secretKey message).wire (signCompact_valid hash secretKey message)),
        true,cycles,117508,121008⟩ := by
  obtain ⟨initial,final,instructions,cycles,loaded,execution,ib,cb,stored,randomizer⟩ :=
    sign_execution hash secretKey cache message
  have run := runWith_of_executes submission hash .sign (secretKey,cache,message) initial instructions
    ⟨.success,final,cycles,117508,121008⟩ loaded execution (by unfold CYCLE_LIMIT; omega)
  have output := SignWire.read_sign hash final secretKey message randomizer stored
  refine ⟨cycles,cb,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x20060 signatureBytes),true,cycles,117508,121008⟩ :
    RunResult (Bytes signatureBytes)) = _
  rw [output]
  rfl

/-- Universal actual signer termination and exact hash-resource accounting. -/
theorem sign_run_bound (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    let result := submission.runWith hash .sign (secretKey,cache,message)
    result.finished=true ∧ result.cycles≤16928763 ∧ result.cycles<CYCLE_LIMIT ∧
      result.hashCalls=117508 ∧ result.hashCompressions=121008 ∧ result.hashCompressions≤BUDGET_SIGN := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash secretKey cache message
  dsimp only
  rw [run]
  dsimp only
  exact ⟨rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_run_refines
end SigGolfCandidate.Hypertree.Signing

end

namespace SigGolfCandidate.Hypertree.Candidate
open SigGolf OracleComp KeygenOrganizer SignatureEncoding
set_option maxRecDepth 4096

theorem expand_exact (hash : Hash) (message : Message) (pk : PublicKey) (signature : Bytes signatureBytes) :
    submission.runWith hash .expand (message,pk,signature)=⟨some signature,true,89733,0,0⟩ := by
  have value := Expansion.run_identity hash (message,pk,signature)
  obtain ⟨finished,_,cycles,calls,blocks⟩ := Expansion.run_bound hash (message,pk,signature)
  cases h : submission.runWith hash .expand (message,pk,signature)
  simp only [h] at value finished cycles calls blocks
  cases value
  cases finished
  cases cycles
  cases calls
  cases blocks
  rfl

/-- Exact deterministic evaluation of a successful organizer pipeline. -/
theorem pipeline_success {σ ω : Type} (hash : Hash) (keygen : OracleComp HashSpec (RunResult (PublicKey×Cache)))
    (sign : PublicKey → Cache → OracleComp HashSpec (RunResult σ))
    (expand : PublicKey → σ → OracleComp HashSpec (RunResult ω))
    (verify : PublicKey → ω → OracleComp HashSpec (RunResult Unit))
    (pk : PublicKey) (cache : Cache) (signature : σ) (witness : ω)
    (kc kh kb sc sh sb ec eh eb vc vh vb : Nat)
    (kg : evalWithAnswerFn hash keygen=⟨some (pk,cache),true,kc,kh,kb⟩)
    (sg : evalWithAnswerFn hash (sign pk cache)=⟨some signature,true,sc,sh,sb⟩)
    (ex : evalWithAnswerFn hash (expand pk signature)=⟨some witness,true,ec,eh,eb⟩)
    (vr : evalWithAnswerFn hash (verify pk witness)=⟨some (),true,vc,vh,vb⟩) :
    evalWithAnswerFn hash (pipeline keygen sign expand verify)=
      ⟨true,fun phase => match phase with | .keygen => kb | .sign => sb | .expand => eb | .verify => vb,vc⟩ := by
  simp only [pipeline,evalWithAnswerFn_bind,kg,sg,ex,vr,evalWithAnswerFn_pure]
  congr 1
  funext phase
  cases phase <;> rfl

/-- Every message succeeds against each single fixed oracle, with exact budgeted-phase costs. -/
theorem honest_exact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks, cycles≤5889440 ∧ calls≤51841 ∧ blocks≤53602 ∧
      evalWithAnswerFn hash (submission.honest secretKey message)=
        ⟨true,fun phase => match phase with | .keygen => 761 | .sign => 121008 | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := Reference.keygen hash secretKey
  let signature := (signCompact hash secretKey message).wire (signCompact_valid hash secretKey message)
  obtain ⟨signCycles,_,signRun⟩ := Signing.sign_run_refines hash secretKey KeygenFunctional.zeroCache message
  obtain ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,verifyRun⟩ := Verifying.run_refines hash pk message signature
  have correct : Reference.verify hash pk message (decode signature).toReference := by
    rw [wire_decode]
    exact signCompact_correct hash secretKey message
  rw [if_pos correct] at verifyRun
  refine ⟨cycles,calls,blocks,by omega,callBound,blockBound,?_⟩
  rw [honest_eq_pipeline]
  exact pipeline_success hash (submission.run .keygen secretKey)
    (fun _ c => submission.run .sign (secretKey,c,message))
    (fun p sig => submission.run .expand (message,p,sig))
    (fun p wit => submission.run .verify (message,p,wit)) pk KeygenFunctional.zeroCache signature signature
    82446 739 761 signCycles 117508 121008 89733 0 0 cycles calls blocks
    (KeygenFunctional.run_exact hash secretKey) signRun (expand_exact hash message pk signature) verifyRun

/-- info: 'SigGolfCandidate.Hypertree.Candidate.honest_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_exact
end SigGolfCandidate.Hypertree.Candidate
