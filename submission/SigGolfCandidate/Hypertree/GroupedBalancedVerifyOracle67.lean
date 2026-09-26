import SigGolfCandidate.Hypertree.GroupedBalancedGraphInteraction67
import SigGolfCandidate.Hypertree.SecurityReference

/-! The exact grouped verifier as a HashSpec oracle computation. Every
bottom, WOTS, Merkle, and index query is emitted at its serialized address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
set_option maxRecDepth 8192

def bottomLeaf (address : Nat) (seed : Reference.Digest) :
    OracleComp HashSpec Reference.Digest :=
  Reference.truncate <$> SecurityReference.ask 2 0 address 0 0 0 (bytes seed)

def node (level address : Nat) (left right : Reference.Digest) :
    OracleComp HashSpec Reference.Digest :=
  Reference.truncate <$> SecurityReference.ask 4 level address 0 0 0
    (bytes left ++ bytes right)

def recoverBottom : (height address index : Nat) →
    GroupedBottomTree.Witness height → OracleComp HashSpec Reference.Digest
  | 0, address, _, .seed seed => bottomLeaf address seed
  | height + 1, address, index, .step inner sibling => do
      if index / 2 ^ height % 2 = 0 then
        let current ← recoverBottom height (2 * address) index inner
        node height address current sibling
      else
        let current ← recoverBottom height (2 * address + 1) index inner
        node height address sibling current

theorem eval_recoverBottom (hash : Hash) (height address index : Nat)
    (witness : GroupedBottomTree.Witness height) :
    evalWithAnswerFn hash (recoverBottom height address index witness) =
      GroupedBottomTree.recover hash height address index witness := by
  induction witness generalizing address index with
  | seed seed => rfl
  | @step height inner sibling ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [recoverBottom, GroupedBottomTree.recover, if_pos bit,
          evalWithAnswerFn_bind, ih]
        rfl
      · simp only [recoverBottom, GroupedBottomTree.recover, if_neg bit,
          evalWithAnswerFn_bind, ih]
        rfl

def chainHash (base leaf : Nat) (chain : Fin 67)
    (step : Nat) (value : Reference.Digest) :
    OracleComp HashSpec Reference.Digest :=
  Reference.truncate <$> SecurityReference.ask 2 base leaf 0 chain.val step
    (bytes value)

def compressLeaf (base leaf : Nat)
    (values : Fin 67 → Reference.Digest) :
    OracleComp HashSpec Reference.Digest :=
  Reference.truncate <$> SecurityReference.ask 3 base leaf 0 0 0
    ((List.ofFn values).flatMap bytes)

def recoverLeaf (base leaf : Nat) (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) :
    OracleComp HashSpec Reference.Digest := do
  let endpoints ← SecurityReference.sequenceFin 67 (fun chain =>
    SecurityReference.walk (chainHash base leaf chain)
      (GroupedBalancedUpperTree67.digit message chain).val
      (GroupedBalancedUpperTree67.maxDigit chain -
        (GroupedBalancedUpperTree67.digit message chain).val)
      (values chain))
  compressLeaf base leaf endpoints

theorem eval_chainHash (hash : Hash) (base leaf : Nat)
    (chain : Fin 67) (step : Nat) (value : Reference.Digest) :
    evalWithAnswerFn hash (chainHash base leaf chain step value) =
      GroupedBalancedUpperTree67.chainHash hash base leaf chain step value := rfl

theorem eval_compressLeaf (hash : Hash) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest) :
    evalWithAnswerFn hash (compressLeaf base leaf values) =
      GroupedBalancedUpperTree67.compressLeaf hash base leaf values := rfl

theorem eval_recoverLeaf (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest) (values : Fin 67 → Reference.Digest) :
    evalWithAnswerFn hash (recoverLeaf base leaf message values) =
      GroupedBalancedUpperTree67.recoverLeaf hash base leaf message values := by
  simp only [recoverLeaf, evalWithAnswerFn_bind,
    SecurityReference.eval_sequenceFin, SecurityReference.eval_walk,
    eval_chainHash, eval_compressLeaf,
    GroupedBalancedUpperTree67.recoverLeaf]

def recoverUpper (base : Nat) : (height address index : Nat) →
    Reference.Digest → GroupedBalancedUpperTree67.Witness height →
      OracleComp HashSpec Reference.Digest
  | 0, address, _, message, .leaf values =>
      recoverLeaf base address message values
  | height + 1, address, index, message, .step inner sibling => do
      if index / 2 ^ height % 2 = 0 then
        let current ← recoverUpper base height (2 * address) index message inner
        node (base + height) address current sibling
      else
        let current ← recoverUpper base height (2 * address + 1) index message inner
        node (base + height) address sibling current

theorem eval_recoverUpper (hash : Hash) (base height address index : Nat)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height) :
    evalWithAnswerFn hash (recoverUpper base height address index message witness) =
      GroupedBalancedUpperTree67.recover hash base height address index
        message witness := by
  induction witness generalizing address index with
  | leaf values => exact eval_recoverLeaf hash base address message values
  | @step height inner sibling ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [recoverUpper, GroupedBalancedUpperTree67.recover,
          if_pos bit, evalWithAnswerFn_bind, ih]
        rfl
      · simp only [recoverUpper, GroupedBalancedUpperTree67.recover,
          if_neg bit, evalWithAnswerFn_bind, ih]
        rfl

def recoverLayers : (heights : List Nat) → (base index : Nat) →
    Reference.Digest → GroupedBalancedScheme67.UpperWitnesses heights →
      OracleComp HashSpec Reference.Digest
  | [], _, _, message, .nil => pure message
  | height :: rest, base, index, message, .cons head tail => do
      let tree := index / 2 ^ height
      let current ← recoverUpper base height tree index message head
      recoverLayers rest (base + height) tree current tail

theorem eval_recoverLayers (hash : Hash) (heights : List Nat)
    (base index : Nat) (message : Reference.Digest)
    (witnesses : GroupedBalancedScheme67.UpperWitnesses heights) :
    evalWithAnswerFn hash
      (recoverLayers heights base index message witnesses) =
    GroupedBalancedScheme67.recoverLayers hash heights base index
      message witnesses := by
  induction witnesses generalizing base index message with
  | nil => rfl
  | @cons height rest head tail ih =>
      simp only [recoverLayers, GroupedBalancedScheme67.recoverLayers,
        evalWithAnswerFn_bind, eval_recoverUpper, ih]

def verify (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature) :
    OracleComp HashSpec Bool := do
  let answer ← SecurityReference.ask 5 0 0 0 0 0
    (bytes (0 : Bytes 16) ++ bytes message ++ bytes signature.randomizer)
  let index : BitVec 160 := answer.extractLsb' 0 160
  let bottomTree := GroupedMixedIndex.bottomTree index
  let bottom ← recoverBottom 10 bottomTree index.toNat signature.bottom
  let root ← recoverLayers GroupedBalancedScheme67.Heights 10 bottomTree
    bottom signature.upper
  pure (decide (root = pk))

theorem eval_verify_iff (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) :
    evalWithAnswerFn hash (verify pk message signature) = true ↔
      GroupedBalancedScheme67.verify hash pk message signature := by
  simp only [verify, evalWithAnswerFn_bind,
    SecurityReference.eval_ask, eval_recoverBottom,
    eval_recoverLayers, evalWithAnswerFn_pure,
    decide_eq_true_eq, GroupedBalancedScheme67.verify,
    Reference.indexOf]

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67
