import SigGolfCandidate.Hypertree.GroupedBalancedSecurityOfficialHybrid67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67

/-! The pure direct67 verifier never calls a private H1 source input. This
lets the source-hit stop monitor attribute hits to public adversary queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifySourceFree67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecuritySourceHybrid67
open GroupedBalancedSecurityOfficialHybrid67
open GroupedBalancedPrivateFactors67
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def SourceFree (secretKey : SecretKey) {α : Type}
    (program : OracleComp World α) : Prop :=
  SecurityCache.stopBefore (SourceHit secretKey) program =
    some <$> program

theorem stopBefore_bind {α β : Type} (secretKey : SecretKey)
    (first : OracleComp World α)
    (next : α → OracleComp World β) :
    SecurityCache.stopBefore (SourceHit secretKey) (first >>= next) =
      (SecurityCache.stopBefore (SourceHit secretKey) first >>= fun value =>
        match value with
        | none => pure none
        | some result =>
            SecurityCache.stopBefore (SourceHit secretKey) (next result)) := by
  induction first using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query continuation ih =>
      rw [bind_assoc,SecurityCache.stopBefore_query_bind,
        SecurityCache.stopBefore_query_bind]
      by_cases hit : SecurityCache.hashBad (SourceHit secretKey) query
      · simp [hit]
      · simp only [if_neg hit, bind_assoc]
        apply bind_congr
        intro answer
        exact ih answer

theorem sourceFree_pure {α : Type} (secretKey : SecretKey)
    (value : α) :
    SourceFree secretKey (pure value : OracleComp World α) := rfl

theorem sourceFree_bind {α β : Type} (secretKey : SecretKey)
    (first : OracleComp World α) (next : α → OracleComp World β)
    (firstFree : SourceFree secretKey first)
    (nextFree : ∀ value, SourceFree secretKey (next value)) :
    SourceFree secretKey (first >>= next) := by
  unfold SourceFree at *
  rw [stopBefore_bind, firstFree]
  simp only [map_eq_bind_pure_comp,bind_assoc]
  apply bind_congr
  intro value
  simpa only [Function.comp_apply,pure_bind,map_eq_bind_pure_comp]
    using nextFree value

theorem stopBefore_bind_free {α β : Type} (secretKey : SecretKey)
    (first : OracleComp World α) (next : α → OracleComp World β)
    (free : SourceFree secretKey first) :
    SecurityCache.stopBefore (SourceHit secretKey) (first >>= next) =
      (first >>= fun value =>
        SecurityCache.stopBefore (SourceHit secretKey) (next value)) := by
  rw [stopBefore_bind, free]
  simp only [map_eq_bind_pure_comp,bind_assoc,Function.comp_apply,pure_bind]

theorem sourceFree_map {α β : Type} (secretKey : SecretKey)
    (program : OracleComp World α) (f : α → β)
    (free : SourceFree secretKey program) :
    SourceFree secretKey (f <$> program) := by
  rw [map_eq_bind_pure_comp]
  exact sourceFree_bind secretKey program (fun value => pure (f value))
    free (fun value => sourceFree_pure secretKey (f value))

theorem sourceFree_query (secretKey : SecretKey)
    (query : Query) (notHit : ¬ SourceHit secretKey query) :
    SourceFree secretKey
      (liftM (World.query (.inr query))) := by
  unfold SourceFree
  simp only [SecurityCache.stopBefore,OracleComp.construct_query,
    SecurityCache.hashBad,notHit,if_false]
  rfl

theorem source_hit_not_addressed (secretKey : SecretKey)
    (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notOne : tag % 256 ≠ 1) (notSix : tag % 256 ≠ 6) :
    ¬ SourceHit secretKey
      (SecurityRandomOracle.addressedInput
        tag level tree leaf chain step payload) := by
  intro hit
  exact (SecurityDomains.not_secretKeyEligible_addressedInput
    tag level tree leaf chain step payload notOne notSix)
    (GroupedBalancedSecuritySourceHybrid67.source_hit_legacy_eligible
      secretKey _ hit)

theorem sourceFree_ask (secretKey : SecretKey)
    (tag level tree leaf chain step : Nat) (payload : List Byte)
    (notOne : tag % 256 ≠ 1) (notSix : tag % 256 ≠ 6) :
    SourceFree secretKey
      ((SecurityReference.ask tag level tree leaf chain step payload).liftComp World) := by
  change SourceFree secretKey
    (liftM (World.query (.inr
      (SecurityRandomOracle.addressedInput
        tag level tree leaf chain step payload))))
  exact sourceFree_query secretKey _
    (source_hit_not_addressed secretKey tag level tree leaf chain step
      payload notOne notSix)

theorem bottomLeaf_free (secretKey : SecretKey)
    (address : Nat) (seed : Reference.Digest) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.bottomLeaf address seed).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.bottomLeaf,
    OracleComp.liftComp_map]
  apply sourceFree_map
  exact sourceFree_ask secretKey 2 0 address 0 0 0 (bytes seed)
    (by norm_num) (by norm_num)

theorem node_free (secretKey : SecretKey)
    (level address : Nat) (left right : Reference.Digest) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.node level address left right).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.node,
    OracleComp.liftComp_map]
  apply sourceFree_map
  exact sourceFree_ask secretKey 4 level address 0 0 0
    (bytes left ++ bytes right) (by norm_num) (by norm_num)

theorem chainHash_free (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67)
    (step : Nat) (value : Reference.Digest) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.chainHash base leaf chain step value).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.chainHash,
    OracleComp.liftComp_map]
  apply sourceFree_map
  exact sourceFree_ask secretKey 2 base leaf 0 chain.val step
    (bytes value) (by norm_num) (by norm_num)

theorem compressLeaf_free (secretKey : SecretKey)
    (base leaf : Nat) (values : Fin 67 → Reference.Digest) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.compressLeaf base leaf values).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.compressLeaf,
    OracleComp.liftComp_map]
  apply sourceFree_map
  exact sourceFree_ask secretKey 3 base leaf 0 0 0
    ((List.ofFn values).flatMap bytes) (by norm_num) (by norm_num)

theorem walk_free {α : Type} (secretKey : SecretKey)
    (body : Nat → α → OracleComp HashSpec α)
    (bodyFree : ∀ step value,
      SourceFree secretKey ((body step value).liftComp World))
    (start count : Nat) (value : α) :
    SourceFree secretKey
      ((SecurityReference.walk body start count value).liftComp World) := by
  induction count generalizing start value with
  | zero => exact sourceFree_pure secretKey value
  | succ count ih =>
      simp only [SecurityReference.walk,OracleComp.liftComp_bind]
      exact sourceFree_bind secretKey _ _ (bodyFree start value)
        (fun next => ih (start + 1) next)

theorem sequenceFin_free {α : Type} (secretKey : SecretKey)
    (n : Nat) (body : Fin n → OracleComp HashSpec α)
    (bodyFree : ∀ i, SourceFree secretKey ((body i).liftComp World)) :
    SourceFree secretKey
      ((SecurityReference.sequenceFin n body).liftComp World) := by
  induction n with
  | zero => exact sourceFree_pure secretKey Fin.elim0
  | succ n ih =>
      simp only [SecurityReference.sequenceFin,OracleComp.liftComp_bind]
      apply sourceFree_bind secretKey _ _ (bodyFree 0)
      intro head
      apply sourceFree_bind secretKey _ _
        (ih (fun i => body i.succ) (fun i => bodyFree i.succ))
      intro tail
      exact sourceFree_pure secretKey
        (Fin.cases head tail : Fin (n + 1) → α)

theorem recoverBottom_free (secretKey : SecretKey)
    (height address index : Nat)
    (witness : GroupedBottomTree.Witness height) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.recoverBottom
        height address index witness).liftComp World) := by
  induction witness generalizing address index with
  | seed seed => exact bottomLeaf_free secretKey address seed
  | @step height inner sibling ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverBottom]
      split
      · simp only [OracleComp.liftComp_bind]
        exact sourceFree_bind secretKey _ _ (ih (2 * address) index)
          (fun current => node_free secretKey height address current sibling)
      · simp only [OracleComp.liftComp_bind]
        exact sourceFree_bind secretKey _ _ (ih (2 * address + 1) index)
          (fun current => node_free secretKey height address sibling current)

theorem recoverLeaf_free (secretKey : SecretKey)
    (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.recoverLeaf
        base leaf message values).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLeaf,
    OracleComp.liftComp_bind]
  apply sourceFree_bind secretKey _ _
  · apply sequenceFin_free
    intro chain
    exact walk_free secretKey
      (GroupedBalancedVerifyOracle67.chainHash base leaf chain)
      (fun step value => chainHash_free secretKey base leaf chain step value)
      (GroupedBalancedUpperTree67.digit message chain).val
      (GroupedBalancedUpperTree67.maxDigit chain -
        (GroupedBalancedUpperTree67.digit message chain).val)
      (values chain)
  · intro endpoints
    exact compressLeaf_free secretKey base leaf endpoints

theorem recoverUpper_free (secretKey : SecretKey)
    (base height address index : Nat)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.recoverUpper
        base height address index message witness).liftComp World) := by
  induction witness generalizing address index message with
  | leaf values => exact recoverLeaf_free secretKey base address message values
  | @step height inner sibling ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverUpper]
      split
      · simp only [OracleComp.liftComp_bind]
        exact sourceFree_bind secretKey _ _
          (ih (2 * address) index message)
          (fun current => node_free secretKey (base + height) address
            current sibling)
      · simp only [OracleComp.liftComp_bind]
        exact sourceFree_bind secretKey _ _
          (ih (2 * address + 1) index message)
          (fun current => node_free secretKey (base + height) address
            sibling current)

theorem recoverLayers_free (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat)
    (message : Reference.Digest)
    (witnesses : GroupedBalancedScheme67.UpperWitnesses heights) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.recoverLayers
        heights base index message witnesses).liftComp World) := by
  induction witnesses generalizing base index message with
  | nil => exact sourceFree_pure secretKey message
  | @cons height rest head tail ih =>
      simp only [GroupedBalancedVerifyOracle67.recoverLayers,
        OracleComp.liftComp_bind]
      exact sourceFree_bind secretKey _ _
        (recoverUpper_free secretKey base height
          (index / 2 ^ height) index message head)
        (fun current => ih (base + height) (index / 2 ^ height) current)

/-- The reference direct67 verifier issues only H5, H2, H3, and H4 queries.
It cannot trigger the public private-source H1 stop monitor. -/
theorem verify_source_free (secretKey : SecretKey)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature) :
    SourceFree secretKey
      ((GroupedBalancedVerifyOracle67.verify
        pk message signature).liftComp World) := by
  simp only [GroupedBalancedVerifyOracle67.verify,
    OracleComp.liftComp_bind]
  apply sourceFree_bind secretKey _ _
    (sourceFree_ask secretKey 5 0 0 0 0 0
      (bytes (0 : Bytes 16) ++ bytes message ++ bytes signature.randomizer)
      (by norm_num) (by norm_num))
  intro answer
  apply sourceFree_bind secretKey _ _
    (recoverBottom_free secretKey 10
      (GroupedMixedIndex.bottomTree (answer.extractLsb' 0 160))
      (answer.extractLsb' 0 160).toNat signature.bottom)
  intro bottom
  apply sourceFree_bind secretKey _ _
    (recoverLayers_free secretKey GroupedBalancedScheme67.Heights 10
      (GroupedMixedIndex.bottomTree (answer.extractLsb' 0 160))
      bottom signature.upper)
  intro root
  exact sourceFree_pure secretKey (decide (root = pk))

theorem semanticSign_source_free (secretKey : SecretKey)
    (table : GroupedBalancedGraphPassive67.PointTable)
    (request : SigningRequest) :
    SourceFree secretKey
      ((GroupedBalancedSecurityJointContext67.semanticSign
        secretKey table request).liftComp World) := by
  simp only [GroupedBalancedSecurityJointContext67.semanticSign,
    OracleComp.liftComp_bind]
  apply sourceFree_bind secretKey _ _
    (sourceFree_query secretKey _
      (source_hit_not_randomizer secretKey request.message))
  intro randomizer
  apply sourceFree_bind secretKey _ _
    (sourceFree_query secretKey _
      (source_hit_not_index secretKey request.message randomizer))
  intro answer
  exact sourceFree_pure secretKey _

#print axioms sourceFree_ask
#print axioms verify_source_free
#print axioms semanticSign_source_free

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityVerifySourceFree67
