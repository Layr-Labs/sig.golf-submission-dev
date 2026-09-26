import SigGolfCandidate.Hypertree.KeygenVerifyCountLayer
import SigGolfCandidate.Hypertree.VerifyLayers
import SigGolfCandidate.Hypertree.VerifyFunctional
import SigGolfCandidate.Hypertree.SecurityBytecodePrograms
import SigGolfCandidate.Hypertree.SecurityBytecodeCounts
import SigGolfCandidate.Hypertree.CandidateHonest

/-! Inlined from SigGolfCandidate.Hypertree.KeygenVerifyCountLayers; its only importer was SigGolfCandidate.Hypertree.SecurityBytecodeReference. -/
section
namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096

theorem verify_layers_exact (hash : Hash) (witness : Bytes signatureBytes) (count level index : Nat)
    (s : MachineState) (current : Reference.Digest)
    (remaining : level+count = 160) (indexSmall : index < 2^192)
    (pc : s.pc = if count = 0 then 0x1220 else 0x1148)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks lastIndex, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34452*count ∧ cycles ≤ 36808*count ∧ calls ≤ 324*count ∧ blocks ≤ 335*count ∧
      final.pc = 0x1220 ∧
      LoopData final 160 lastIndex (Reference.recoverLayers hash level index current (wireLayers witness count level)) witness ∧
      LowFrame s final ∧
      calls = SecurityVerifyCost.layersCalls hash level index current (wireLayers witness count level) := by
  induction count generalizing level index s current with
  | zero =>
    have levelEq : level = 160 := by omega
    subst level
    exact ⟨s, 0, 0, 0, 0, index, Trace.refl _, by decide, by decide, by decide, by decide, by simpa using pc, data,
      (fun _ _ _ => rfl), rfl⟩
  | succ count ih =>
    have small : level < 160 := by omega
    obtain ⟨next, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, nextPC, nextData, frame, countEq⟩ :=
      verify_layer_exact hash s level index current witness (by simpa using pc) small indexSmall data
    have nextPC' : next.pc = if count = 0 then 0x1220 else 0x1148 := by
      have eq : level+1 = 160 ↔ count = 0 := by omega
      simpa only [eq] using nextPC
    obtain ⟨final, tailSteps, tailCycles, tailCalls, tailBlocks, lastIndex, tailRun, tsteps, tcycles, tcalls, tblocks,
      finalPC, finalData, tailFrame, tailCount⟩ := ih (level+1) (index/2) next
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level))
        (by omega) (by omega) nextPC' nextData
    refine ⟨final, steps+tailSteps, cycles+tailCycles, calls+tailCalls, blocks+tailBlocks, lastIndex,
      run.trans tailRun, ?_, ?_, ?_, ?_, finalPC, finalData, frame.trans s next final tailFrame, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · simp only [wireLayers,SecurityVerifyCost.layersCalls]
      rw [countEq,tailCount]

end SigGolfCandidate.Hypertree.KeygenVerifyCount
end

/-! Inlined from SigGolfCandidate.Hypertree.KeygenVerifyCountRun; its only importer was SigGolfCandidate.Hypertree.SecurityBytecodeReference. -/
section
namespace SigGolfCandidate.Hypertree.KeygenVerifyCount
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

theorem loaded_recovery_exact (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial recovered steps cycles calls blocks,
      initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial steps cycles calls blocks recovered ∧
      steps ≤ 5512450 ∧ cycles ≤ 5889425 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      recovered.pc = 0x1220 ∧
      (RootMatches recovered ↔ Reference.verify hash pk message (SignatureEncoding.decode witness).toReference) ∧
      calls = SecurityVerifyCost.verifyCalls hash message (SignatureEncoding.decode witness) := by
  obtain ⟨initial, ready, loaded, pre, pc, data, preFrame⟩ := loaded_loop_data hash pk message witness
  let index := (Reference.indexOf hash message (SignatureEncoding.decode witness).randomizer).toNat
  have indexSmall : index < 2^192 := by
    have h := (Reference.indexOf hash message (SignatureEncoding.decode witness).randomizer).isLt
    dsimp [index]
    omega
  obtain ⟨recovered, steps, cycles, calls, blocks, lastIndex, run, hsteps, hcycles, hcalls, hblocks, finalPC, finalData, frame, countEq⟩ :=
    verify_layers_exact hash witness 160 0 index ready 0 rfl indexSmall (by simpa using pc) data
  have allFrame := preFrame.trans initial ready recovered frame
  have pkWords : ∀ i : Fin 2, recovered.getMem (wordAddress 0x40 i.val) = pk.extractLsb' (64*i.val) 64 := by
    intro i
    have same := allFrame (0x40+8*i.val) (by omega) (by have := i.isLt; omega)
    change recovered.getMem (wordAddress 0x40 i.val) = initial.getMem (wordAddress 0x40 i.val) at same
    rw [same]
    exact loaded_publicKey_word pk message witness initial loaded i
  have matchRoot := root_matches_iff recovered _ pk finalData.currentEq pkWords
  refine ⟨initial, recovered, 130+steps, 145+cycles, 1+calls, 2+blocks,
    loaded, pre.trans run, by omega, by omega, by omega, by omega, finalPC, ?_, ?_⟩
  · rw [matchRoot, wire_layers_decode]
    have length : (SignatureEncoding.decode witness).toReference.layers.length = 160 := by
      simp [SignatureEncoding.decode, SignatureEncoding.Compact.toReference]
    simp only [Reference.verify, length, true_and]
    rfl

  · rw [countEq,wire_layers_decode]
    rfl

/-- Universal bytecode refinement, including malformed witnesses and exact accept/reject behavior. -/
theorem run_refines_exact (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ cycles calls blocks, cycles ≤ 5889440 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      submission.runWith hash .verify (message, pk, witness) =
        ⟨if Reference.verify hash pk message (SignatureEncoding.decode witness).toReference then some () else none,
          true, cycles, calls, blocks⟩ ∧
      calls = SecurityVerifyCost.verifyCalls hash message (SignatureEncoding.decode witness) := by
  classical
  obtain ⟨initial, recovered, steps, cycles, calls, blocks, loaded, run, hsteps, hcycles, hcalls, hblocks, pc, accepted, countEq⟩ :=
    loaded_recovery_exact hash pk message witness
  obtain ⟨tailSteps, final, tailBound, tailRun, _⟩ := verify_footer_executes hash recovered pc
  have execution := run.then_executes tailRun
  have actual := runWith_of_executes submission hash .verify (message, pk, witness) initial (steps+tailSteps)
    _ loaded execution (by change steps+tailSteps ≤ 2^32; omega)
  refine ⟨cycles+tailSteps, calls, blocks, by omega, hcalls, hblocks, ?_, countEq⟩
  rw [actual]
  by_cases yes : RootMatches recovered
  · have valid := accepted.mp yes
    simp only [if_pos yes, if_pos valid, Execution.charge, Nat.add_zero]
    rfl
  · have invalid : ¬Reference.verify hash pk message (SignatureEncoding.decode witness).toReference :=
      fun h => yes (accepted.mpr h)
    simp only [if_neg yes, if_neg invalid, Execution.charge, Nat.add_zero]
    rfl

/-- The protected typed verifier's HASH calls exactly match the reference cost. -/
theorem run_calls (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    (submission.runWith hash .verify (message,pk,witness)).hashCalls =
      SecurityVerifyCost.verifyCalls hash message (SignatureEncoding.decode witness) := by
  obtain ⟨cycles,calls,blocks,_,_,_,run,count⟩ := run_refines_exact hash pk message witness
  rw [run]
  exact count

theorem run_calls_reference (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    (submission.runWith hash .verify (message,pk,witness)).hashCalls =
      SecurityVerifyCost.calls hash (SecurityVerify.verifyCompact pk message (SignatureEncoding.decode witness)) := by
  rw [run_calls,SecurityVerifyCost.calls_verifyCompact]

/-- info: 'SigGolfCandidate.Hypertree.KeygenVerifyCount.run_calls_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_calls_reference

end SigGolfCandidate.Hypertree.KeygenVerifyCount

end

namespace SigGolfCandidate.Hypertree.SecurityBytecode
open SigGolf OracleComp OracleSpec SecurityCache SecurityGraphHidden SecurityVerifyCost SignatureEncoding
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def countHash {α : Type} (program : OracleComp HashSpec α) : OracleComp HashSpec (α×Nat) :=
  OracleComp.construct (fun value => pure (value,0))
    (fun input _ next => do
      let answer ← liftM (HashSpec.query input)
      let result ← next answer
      pure (result.1,result.2+1)) program

@[simp] theorem countHash_pure {α : Type} (value : α) : countHash (pure value)=pure (value,0) := rfl

theorem countHash_query_bind {α : Type} (input : Query) (next : BitVec 256 → OracleComp HashSpec α) :
    countHash (liftM (HashSpec.query input) >>= next) = (do
      let answer ← liftM (HashSpec.query input)
      let result ← countHash (next answer)
      pure (result.1,result.2+1)) := rfl

@[simp] theorem eval_countHash {α : Type} (hash : Hash) (program : OracleComp HashSpec α) :
    evalWithAnswerFn hash (countHash program)=(evalWithAnswerFn hash program,calls hash program) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    simp only [countHash_query_bind,evalWithAnswerFn_bind,evalWithAnswerFn_pure,ih,calls_query_bind]
    rfl

def referenceSign (secretKey : SecretKey) (request : SigningRequest) :
    OracleComp HashSpec (Option (Bytes submission.sizes.signature)×Nat) :=
  countHash (SecurityExperiment.serialize <$> SecurityReference.signCompact secretKey request.message)

def referenceKeygen (secretKey : SecretKey) : OracleComp HashSpec (Option (PublicKey×Cache)×Nat) := do
  let result ← countHash (SecurityReference.keygen secretKey)
  pure (some (result.1,KeygenFunctional.zeroCache),result.2)

def referenceCheck (pk : PublicKey) (transcript : Transcript submission.sizes) :
    Forgery submission.sizes → OracleComp HashSpec AttackResult
  | .witness message witness => do
      let result ← countHash (SecurityVerify.verifyCompact pk message (decode witness))
      pure ⟨result.1 && transcript.freshMessage message,transcript.hashCalls+result.2⟩
  | .signature message signature => do
      let result ← countHash (SecurityVerify.verifyCompact pk message (decode signature))
      pure ⟨result.1 && transcript.freshSignature message signature,transcript.hashCalls+result.2⟩

def referenceInterface : Interface where
  keygen := referenceKeygen
  sign := referenceSign
  check := referenceCheck

theorem keygen_equivalent (hash : Hash) (secretKey : SecretKey) :
    evalWithAnswerFn hash (actualInterface.keygen secretKey)=evalWithAnswerFn hash (referenceInterface.keygen secretKey) := by
  simp only [actualInterface,referenceInterface,referenceKeygen,evalWithAnswerFn_map,evalWithAnswerFn_bind,
    evalWithAnswerFn_pure,eval_countHash,SecurityReference.eval_keygen,SecurityBytecodeCounts.calls_keygen]
  change view (submission.runWith hash .keygen secretKey)=_
  rw [KeygenFunctional.run_exact]
  rfl

theorem sign_equivalent (hash : Hash) (secretKey : SecretKey) (request : SigningRequest) :
    evalWithAnswerFn hash (actualInterface.sign secretKey request)=
      evalWithAnswerFn hash (referenceInterface.sign secretKey request) := by
  obtain ⟨cycles,_,run⟩ := Signing.sign_run_refines hash secretKey request.cache request.message
  simp only [actualInterface,referenceInterface,referenceSign,eval_countHash,evalWithAnswerFn_map,
    SecurityReference.eval_signCompact,SecurityExperiment.serialize_valid _ (signCompact_valid _ _ _),
    calls_map,SecurityBytecodeCounts.calls_signCompact]
  change view (submission.runWith hash .sign (secretKey,request.cache,request.message))=_
  rw [run]
  rfl

theorem check_equivalent (hash : Hash) (pk : PublicKey) (transcript : Transcript submission.sizes)
    (forgery : Forgery submission.sizes) :
    evalWithAnswerFn hash (actualInterface.check pk transcript forgery)=
      evalWithAnswerFn hash (referenceInterface.check pk transcript forgery) := by
  classical
  cases forgery with
  | witness message witness =>
    obtain ⟨cycles,vcalls,blocks,_,_,_,run⟩ := Verifying.run_refines hash pk message witness
    have counted := KeygenVerifyCount.run_calls_reference hash pk message witness
    rw [run] at counted
    simp only [actualInterface,referenceInterface,Submission.checkForgery,referenceCheck,
      evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_countHash]
    change (⟨(submission.runWith hash .verify (message,pk,witness)).value.isSome && _,
      transcript.hashCalls+(submission.runWith hash .verify (message,pk,witness)).hashCalls⟩ : AttackResult)=_
    rw [run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]
  | signature message signature =>
    obtain ⟨cycles,vcalls,blocks,_,_,_,run⟩ := Verifying.run_refines hash pk message signature
    have counted := KeygenVerifyCount.run_calls_reference hash pk message signature
    rw [run] at counted
    simp only [actualInterface,referenceInterface,Submission.checkForgery,referenceCheck,
      evalWithAnswerFn_bind,evalWithAnswerFn_pure,eval_countHash]
    have ex : evalWithAnswerFn hash (submission.run .expand (message,pk,signature)) =
        ⟨some signature,true,89733,0,0⟩ := Candidate.expand_exact hash message pk signature
    simp only [ex,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
    change (⟨(submission.runWith hash .verify (message,pk,signature)).value.isSome && _,
      transcript.hashCalls+0+(submission.runWith hash .verify (message,pk,signature)).hashCalls⟩ : AttackResult)=_
    rw [run,counted]
    split <;> simp_all [SecurityVerify.eval_verifyCompact_iff]

end SigGolfCandidate.Hypertree.SecurityBytecode
