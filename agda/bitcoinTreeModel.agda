
module bitcoinTreeModel where

-- open import bool
open import libraries.listLib
open import libraries.natLib
open import libraries.finLib
open import Data.Nat
open import Data.Empty
open import Data.Fin hiding (_+_ ; _≤_ )
open import Data.List
open import Data.Unit hiding (_≤_ )
open import Data.Bool
open import Data.Product
open import Data.Nat.Base
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


-- #####################################
-- #  Preliminaries                    #
-- #####################################


infixr 3 _+msg_

Time : Set
Time = ℕ

Amount : Set
Amount = ℕ

Address : Set
Address = ℕ

TXID : Set
TXID = ℕ

Signature : Set
Signature  =  ℕ

PublicKey : Set
PublicKey  =  ℕ

-- \bitcoinVersSix
data Msg : Set where
   nat : (n : ℕ) → Msg
   _+msg_ : (m m' : Msg) → Msg
   list : (l  : List Msg) → Msg

postulate hashMsg : Msg → ℕ

-- +msg could be replaced by a list with two elements; we use +msg
-- since it is closer to how messages are serialised where
-- a list requires an extra length argument.x

-- \bitcoinVersSix
-- already in \bitcoinVersFive
postulate publicKey2Address : (pubk : PublicKey) → Address

-- Signed means that Msg msg has been signed
-- by private key corresponding to pubk

-- \bitcoinVersSix
-- already in \bitcoinVersFive
postulate Signed : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set
-- postulate sign2ℕ : (msg : Msg)(addr : Address)(s : Signed msg addr)
--                    → ℕ

-- \bitcoinVersSix
postulate minerReward : (t : Time) → Amount
postulate blockMaturationTime : Time
-- reward for miner at time t
-- how long the miner needs to wait before his reward can be spent
-- should be 101


-- #############################################################################
-- #  Inductive-Recursive Definition of                                        #
-- #       Transaction Tree, Transactions, and                                 #
-- #  Unspent Transaction Outputs                                              #
-- #############################################################################

-- \bitcoinVersSix
record TXOutputfield : Set where
  constructor txOutputfield
  field  amount : Amount
         address : Address
open TXOutputfield public


mutual
-- \bitcoinVersSix
  data TXTree  : Set where
    genesisTree  :  TXTree
    txtree       :  (tree : TXTree)(tx : TX tree) → TXTree

-- \bitcoinVersSix
  data TX (tr : TXTree) :  Set where
     normalTX  :  (inputs   :  TxInputs tr)  (outputs  :  List TXOutputfield)  → TX tr
     coinbase  :  (time : Time)              (outputs  :  List TXOutputfield)  → TX tr

-- \bitcoinVersSix
  record TXOutput : Set where
    inductive
    constructor txOutput
    field  trTree   : TXTree
           tx       : TX trTree
           output   : Fin (nrOutputs trTree  tx)


-- \bitcoinVersSix
  utxoMinusNewInputs : (tr : TXTree)(tx : TX tr) → List TXOutput
  utxo : (tr : TXTree) → List TXOutput

-- \bitcoinVersSix
  TxInputs : (tr : TXTree) → Set
  TxInputs tr = SubList+ (PublicKey ×  Signature) (utxo tr)

-- \bitcoinVersSix
  utxoMinusNewInputs tr (normalTX inputs outputs)  =  listMinusSubList+ (utxo tr) inputs
  utxoMinusNewInputs tr (coinbase time outputs)    =  utxo tr

  utxo genesisTree     =  []
  utxo (txtree tr tx)  =  utxoMinusNewInputs tr tx ++ tx2TXOutputs tr tx

--(normalTX inp outp)) =
--           listMinusSubList+ (utxo tr) inp ++ tx2TXOutputs tr  (normalTX inp outp)
--  utxo (txtree tr (coinbase t outp)) = utxo tr ++ tx2TXOutputs tr  (coinbase t outp)


-- \bitcoinVersSix
  tx2TXOutputs : (tr : TXTree)(tx : TX tr) → List TXOutput
  tx2TXOutputs tr tx  = mapL (λ i → txOutput tr tx i)(listOfElementsOfFin (nrOutputs tr tx))

-- \bitcoinVersSix
  nrOutputs : (tr : TXTree) (tx : TX tr) → ℕ

  nrOutputs tr (normalTX inp outp) = length outp
  nrOutputs tr (coinbase t outp) = length outp



open TXOutput public
open TXTree public
open TX public


-- #############################################################################
-- #  Computing Sum of Inputs and Outputs of Transactions and Transaction Fees #
-- #############################################################################

-- \bitcoinVersSix
outputs2SumAmount : List TXOutputfield → Amount
outputs2SumAmount l = sumListViaf amount l

tx2SumOutputs : {tr : TXTree}(tx : TX tr) → Amount
tx2SumOutputs (normalTX inputs outputs) = outputs2SumAmount outputs
tx2SumOutputs (coinbase time outputs) =  outputs2SumAmount outputs


-- \bitcoinVersSix
txOutput2Outputfield : TXOutput → TXOutputfield
txOutput2Outputfield (txOutput trTree (normalTX inputs outputs) i) = nth outputs i
txOutput2Outputfield (txOutput trTree (coinbase time outputs) i)   = nth outputs i

txOutput2Amount : TXOutput → Amount
txOutput2Amount output = amount (txOutput2Outputfield output)

txOutput2Address : TXOutput → Address
txOutput2Address output = address (txOutput2Outputfield output)


-- \bitcoinVersSix
inputs2PrevOutputsSigPbk :  (tr : TXTree)(inputs : TxInputs tr)
                            → List (TXOutput × PublicKey × Signature)
inputs2PrevOutputsSigPbk tr inputs = subList+2List inputs

inputs2PrevOutputs : (tr : TXTree)(inputs : TxInputs tr) → List TXOutput
inputs2PrevOutputs tr inputs = mapL proj₁ (inputs2PrevOutputsSigPbk tr inputs)

inputs2Sum : (tr : TXTree)(inputs : TxInputs tr) → Amount
inputs2Sum  tr inputs = sumListViaf txOutput2Amount (inputs2PrevOutputs tr inputs)

-- \bitcoinVersSix
txTree2TimeNextTobeMinedBlock : (tr : TXTree) → Time
txTree2TimeNextTobeMinedBlock genesisTree = 0
txTree2TimeNextTobeMinedBlock (txtree tree (normalTX inputs outputs)) =
            txTree2TimeNextTobeMinedBlock tree
txTree2TimeNextTobeMinedBlock (txtree tree (coinbase time outputs)) = suc time

-- \bitcoinVersSix
mutual
  tx2SumInputs : (tr : TXTree)(tx : TX tr) → Amount
  tx2SumInputs tr (normalTX inputs outputs) = inputs2Sum tr inputs
  tx2SumInputs tr (coinbase time outputs) =
     txTree2RecentTXFees tr + minerReward (txTree2TimeNextTobeMinedBlock tr)

  txTree2RecentTXFees : (tr : TXTree) → Amount
  txTree2RecentTXFees genesisTree = 0
  txTree2RecentTXFees (txtree tr (normalTX inputs outputs)) =
     txTree2RecentTXFees tr + (inputs2Sum tr inputs ∸ outputs2SumAmount outputs)
  txTree2RecentTXFees (txtree tr (coinbase time outputs)) = 0

-- \bitcoinVersSix
output2MaturationTime : TXOutput → Time
output2MaturationTime (txOutput trTree (normalTX inputs outputs) i) = 0
output2MaturationTime (txOutput trTree (coinbase time outputs) i) = time + blockMaturationTime


-- ##############################################################
-- #  Computing Messages to be Signed and Transaction IDs       #
-- ##############################################################

-- \bitcoinVersSix
txOutputfield2Msg : TXOutputfield → Msg
txOutputfield2Msg (txOutputfield amount₁ address₁) = nat amount₁ +msg nat address₁

outputFields2Msg : (outp : List TXOutputfield) → Msg
outputFields2Msg outp = list (mapL txOutputfield2Msg outp)

mutual

-- \bitcoinVersSix
  tx2Msg : (tr : TXTree)(tx : TX tr) → Msg
  tx2Msg tr (normalTX inputs₁ outputs₁) =  list (mapL utxoIndexSig2Msg inputIndices)
                                           +msg outputFields2Msg outputs₁
      where
         inputIndices : List (Fin (length (utxo tr)) × PublicKey × Signature)
         inputIndices = subList+2IndicesOriginalList (utxo tr) inputs₁

         utxoIndexSig2Msg : Fin (length (utxo tr)) × PublicKey × Signature → Msg
         utxoIndexSig2Msg (i , (pbk , sig)) = utxo2Msg tr i +msg nat pbk +msg nat sig

  tx2Msg tr (coinbase time outputs₁) = nat time +msg outputFields2Msg outputs₁

-- \bitcoinVersSix
  tx2id : (tr : TXTree)(tx : TX tr) → ℕ
  tx2id tr tx = hashMsg (tx2Msg tr tx)

  -- note time included following the fix for nonuniqueness of ids
  -- in \cite{github:bip-0034.mediawiki}

-- \bitcoinVersSix
  utxoMinusNewInputs2Msg : (tr : TXTree)(tx : TX tr)(i : Fin (length (utxoMinusNewInputs tr tx)))
                   → Msg
  utxoMinusNewInputs2Msg tr (normalTX inputs outputs) i = utxo2Msg tr (listMinusSubList+Index2OrgIndex (utxo tr) inputs i)
  utxoMinusNewInputs2Msg tr (coinbase time outputs) i = utxo2Msg tr i

    -- listMinusSubList+Index2OrgIndex
    -- will map the result of deleting entries indices to the original
    -- entries
    -- we now need to add as well the new indices

-- \bitcoinVersSix
  utxo2Msg : (tr : TXTree)(i : Fin (length (utxo tr))) → Msg
  utxo2Msg genesisTree ()
  utxo2Msg (txtree tr tx) = concatListIndex2OriginIndices l₀ l₁ f₀ f₁
    module utxo2Msgaux where
        l₀ : List TXOutput
        l₀ = utxoMinusNewInputs tr tx

        l₁ : List TXOutput
        l₁ = tx2TXOutputs tr tx

        f₀ : Fin (length l₀)  → Msg
        f₀ i = utxoMinusNewInputs2Msg tr tx i

        f₁ : Fin (length l₁) → Msg
        f₁ i = nat (tx2id tr tx) +msg nat (toℕ i)



-- msg to be signed is what needs to be signed by the user
-- in \cite{derosa:theFirstTransacationPt1} he writes:\\
-- In practice, for each input I, the message to be signed is a slightly modified version of the transaction where:
-- -  The I script is set to the output script of the UTXO it refers to.
-- - Input scripts other than I are truncated to zero-length.
-- - A SIGHASH flag is appended.
--
-- since in our case the output scrpt is epresented by by the address in the
--   txoutput field, we get the following:

-- \bitcoinVersSix
-- unused
txOutput2Msg : (txout  : TXOutput) → Msg
txOutput2Msg (txOutput tr tx i) = nat (tx2id tr tx) +msg nat (toℕ i)



-- \bitcoinVersSix
msgToBeSignedByInput : (txoutput : TXOutput)(outputs    : List TXOutputfield) → Msg
msgToBeSignedByInput txoutput outputs =
                   (nat (tx2id (trTree txoutput) (tx txoutput)) +msg
                    nat (toℕ (output txoutput)) +msg
                    nat (txOutput2Address txoutput)) +msg
                   outputFields2Msg outputs

 -- first item is the id of previous transaction
 -- second item is the nr of the output within this transaction
 -- thrid item is the output address of this transcation
 -- last item is the essage for the outputs

                           -- address
                           -- with script it would be
                           --   the scriptPubKey of the output
                           -- here it is the address

-- \bitcoinVersSix
CorrectTX : (tr : TXTree)(tx : TX tr) → Set
CorrectTX tr (normalTX inputs outputs) =
         NonNil (inputs2PrevOutputs tr inputs) ×
         NonNil outputs ×
         (inputs2Sum tr inputs ≥  outputs2SumAmount outputs) ×
         (∀inList (inputs2PrevOutputs tr inputs)
                  (λ o → output2MaturationTime o ≤ txTree2TimeNextTobeMinedBlock tr)) ×
         (∀inList (inputs2PrevOutputsSigPbk tr inputs)
            (λ {(outp , pbk , sign) →
                publicKey2Address pbk ≡ txOutput2Address outp ×
                Signed (msgToBeSignedByInput outp outputs) pbk sign  }))

CorrectTX tr (coinbase time outputs) =
         NonNil outputs ×
         outputs2SumAmount outputs ≡ txTree2RecentTXFees tr + minerReward time ×
         time ≡ txTree2TimeNextTobeMinedBlock tr
--         (∀inList (inputs2PrevOutputs tr inputs)
--                  (λ o → output2MaturationTime o ≤ txTree2TimeNextTobeMinedBlock tr)) ×
         -- expresses that inputs are spendable after maturation time

--         (∀inList (inputs2PrevOutputsSigPbk tr inputs)
--            (λ {(outp , pbk , sign) →
--                publicKey2Address pbk ≡ txOutput2Address outp ×
--                Signed (msgToBeSignedByInput outp
--                                             outputs) pbk sign  }))

         -- expresses that public keys in the input have address of the input
         --   and the input msg is signed by the private key of this public key





-- \bitcoinVersSix
CorrectTxTree : (tr : TXTree) → Set
CorrectTxTree genesisTree = ⊤
CorrectTxTree (txtree tr tx) = CorrectTxTree tr × CorrectTX tr tx

record TXTreeCorrect : Set where
  constructor txTreeCorrect
  field  txtr     :  TXTree
         corTxtr  :  CorrectTxTree txtr


open TXTreeCorrect public

-- \bitcoinVersSix
record TXcorrect (tr : TXTreeCorrect) : Set where
  field   theTx  :  TX (tr .txtr)
          corTx  :  CorrectTX (tr .txtr) theTx

open TXcorrect public

-- \bitcoinVersSix
initialTxTreeCorrect : TXTreeCorrect
initialTxTreeCorrect = txTreeCorrect genesisTree tt

addTxtreeCorrect : (tr : TXTreeCorrect)(tx : TXcorrect tr) → TXTreeCorrect
addTxtreeCorrect tr tx =
    txTreeCorrect (txtree (tr .txtr) (tx .theTx)) (tr .corTxtr , tx .corTx)

-- ##############################################################
-- #  Merkle Trees                                              #
-- ##############################################################


-- \bitcoinVersSix
record MerkleInputField : Set where
  constructor inputField
  field  txid          : TXID
         outputNr      : ℕ
         publicKey     : PublicKey
         signature     : Signature

-- \bitcoinVersSix
record MerkleTXcoinbase : Set where
  constructor merkleCoinbase
  field  time     :  Time
         outputs  :  List TXOutputfield

record MerkleTXstandard : Set where
  constructor merkleTXstd
  field  inputs   :  List MerkleInputField
         outputs  :  List TXOutputfield

data MerkleTX : Set where
  txcoinbase  :  MerkleTXcoinbase  →  MerkleTX
  txstd       :  MerkleTXstandard  →  MerkleTX





open MerkleInputField public
open MerkleTXstandard public
open MerkleTXcoinbase public

-- \bitcoinVersSix
txOutpSign2MerkleInput : TXOutput × PublicKey × Signature → MerkleInputField
txOutpSign2MerkleInput (txOutput tr tx₁ i , pbk , sign) = inputField (tx2id tr tx₁) (toℕ i) pbk sign

txInputs2MerkleInputs : (tr : TXTree)(txInputs : TxInputs tr) → List MerkleInputField
txInputs2MerkleInputs tr txin =  mapL txOutpSign2MerkleInput (inputs2PrevOutputsSigPbk tr txin)

-- \bitcoinVersSix
MerkleTXCorresponds2TX : (tx : MerkleTX)(tr : TXTree)(tx : TX tr) → Set
MerkleTXCorresponds2TX (txcoinbase (merkleCoinbase time₁ outputs₁)) tr (coinbase time₂ outputs₂)
       = time₁ ≡ time₂ × outputs₁ ≡ outputs₂
MerkleTXCorresponds2TX (txstd (merkleTXstd inputs₁ outputs₁)) tr (normalTX inputs₂ outputs₂)
       = inputs₁ ≡ txInputs2MerkleInputs tr inputs₂ × outputs₁ ≡ outputs₂
MerkleTXCorresponds2TX (txcoinbase x) tr (normalTX inputs₁ outputs₁)  =  ⊥
MerkleTXCorresponds2TX (txstd x) tr (coinbase time₁ outputs₁)         =  ⊥

-- \bitcoinVersSix
record MerkleTXCor (tr : TXTreeCorrect) : Set where
  field  mk   : MerkleTX
         mtx  : TXcorrect tr
         cor  : MerkleTXCorresponds2TX mk (tr .txtr) (mtx .theTx)

open MerkleTXCor public

-- \bitcoinVersSix
updateTXTree : (tr : TXTreeCorrect)(m : MerkleTXCor tr) → TXTreeCorrect
updateTXTree tr m = addTxtreeCorrect tr (m .mtx)
