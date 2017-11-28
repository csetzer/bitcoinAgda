

module bitcoinLedgerModel where

-- open import bool
open import libraries.listLib
open import libraries.natLib
open import Data.Nat
open import Data.List
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat.Base

infixr 3 _+msg_

Time : Set
Amount : Set
Address : Set
TXID : Set
Signature : Set
PublicKey : Set

-- \bitcoinVersFive
Time       =  ℕ
Amount     =  ℕ

Address    =  ℕ
TXID       =  ℕ
Signature  =  ℕ
PublicKey  =  ℕ


-- \bitcoinVersFive
data Msg : Set where
   nat     :  (n : ℕ)         → Msg
   _+msg_  :  (m m' : Msg)     → Msg
   list    :  (l  : List Msg)  → Msg

postulate hashMsg : Msg → ℕ



-- \bitcoinVersFive
postulate publicKey2Address : (pubk : PublicKey) → Address

-- Signed means that Msg msg has been signed
-- by private key corresponding to pubk

-- \bitcoinVersFive
postulate Signed : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set

record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
  field  publicKey  :  PublicKey
         pbkCorrect :  publicKey2Address publicKey ≡ℕ  address
         signature  :  Signature
         signed     :  Signed msg publicKey signature

{-
_≡PbkBool_ : (pubk pubk' : PublicKey) → Bool
pubk ≡PbkBool pubk' = publicKey2Address pubk  ≡ℕb publicKey2Address pubk'
-}

{- -- Unused but correct code

_≡Pbk_ : PublicKey → PublicKey → Set
key1 ≡Pbk key2 = T (key1 ≡PbkBool key2)
-}

-- \bitcoinVersFive
record TXField : Set where
  constructor txField
  field  amount     :  Amount
         address    :  Address

open TXField public

--\bitcoinVersFive
txField2Msg : (inp : TXField) → Msg
txField2Msg inp  =   nat (amount inp) +msg nat (address inp)

txFieldList2Msg : (inp : List TXField) → Msg
txFieldList2Msg inp  = list (mapL txField2Msg inp)


-- \bitcoinVersFive
txFieldList2TotalAmount : (inp : List TXField) → Amount
txFieldList2TotalAmount inp = sumListViaf amount inp

-- \bitcoinVersFive
record TXUnsigned : Set where
  field  inputs   : List TXField
         outputs  : List TXField

open TXUnsigned public

-- \bitcoinVersFive
txUnsigned2Msg :  (transac : TXUnsigned) → Msg
txUnsigned2Msg transac = txFieldList2Msg (inputs transac)  +msg txFieldList2Msg (outputs transac)

-- \bitcoinVersFive
txInput2Msg : (inp : TXField)(outp : List TXField) → Msg
txInput2Msg inp outp = txField2Msg inp +msg txFieldList2Msg outp

-- \bitcoinVersFive
tx2Signaux : (inp : List TXField) (outp : List TXField)  → Set
tx2Signaux [] outp = ⊤
tx2Signaux (inp ∷ restinp) outp =
    SignedWithSigPbk (txInput2Msg inp outp) (address inp) ×  tx2Signaux restinp outp

tx2Sign : TXUnsigned → Set
tx2Sign tr = tx2Signaux (inputs tr) (outputs tr)


-- \bitcoinVersFive
record TX : Set where
  field  tx       :  TXUnsigned
         cor      : txFieldList2TotalAmount (inputs tx) ≥ txFieldList2TotalAmount (outputs tx)
         nonEmpt  : NonNil (inputs tx) × NonNil (outputs tx)
         sig      : tx2Sign tx

open TX public

LedgerR : Set

-- \bitcoinVersFive
LedgerR = (addr : Address) → Amount

initialLedger : LedgerR
initialLedger addr = 0

-- \bitcoinVersFive
addTXFieldToLedgerR :  (tr : TXField)(oldLedgerR : LedgerR) → LedgerR
addTXFieldToLedgerR  tr oldLedgerR pubk =
         if   pubk ≡ℕb address tr then oldLedgerR pubk +  amount tr else oldLedgerR pubk

addTXFieldListToLedgerR  :  (tr : List TXField)(oldLedgerR : LedgerR) → LedgerR
addTXFieldListToLedgerR []        oldLedgerR  =  oldLedgerR
addTXFieldListToLedgerR (x ∷ tr)  oldLedgerR  =
      addTXFieldListToLedgerR tr (addTXFieldToLedgerR x oldLedgerR)


-- \bitcoinVersFive
subtrTXFieldFromLedgerR      :  (tr : TXField) (oldLedgerR : LedgerR) → LedgerR
subtrTXFieldListFromLedgerR  :  (tr : List TXField)(oldLedgerR : LedgerR)→ LedgerR
subtrTXFieldFromLedgerR  tr oldLedgerR pubk =
         if   pubk ≡ℕb address tr
         then oldLedgerR pubk ∸  amount tr
         else oldLedgerR pubk

subtrTXFieldListFromLedgerR [] oldLedgerR = oldLedgerR
subtrTXFieldListFromLedgerR (x ∷ tr) oldLedgerR =
           subtrTXFieldListFromLedgerR tr (subtrTXFieldFromLedgerR x oldLedgerR)

-- \bitcoinVersFive
updateLedgerRByTX :  (tr : TX)(oldLedgerR : LedgerR) → LedgerR
updateLedgerRByTX tr oldLedgerR =  addTXFieldListToLedgerR (outputs (tx tr))
                                   (subtrTXFieldListFromLedgerR (inputs (tx tr)) oldLedgerR )


-- \bitcoinVersFive
correctInput : (tr : TXField) (ledgerR : LedgerR) → Set
correctInput tr ledgerR = ledgerR (address tr) ≥ amount tr

-- \bitcoinVersFive
correctInputs : (tr : List TXField) (ledgerR : LedgerR) → Set
correctInputs [] ledgerR = ⊤
correctInputs (x ∷ tr) ledgerR = correctInput x ledgerR
                                × correctInputs tr (subtrTXFieldFromLedgerR x ledgerR)

correctTX : (tr : TX) (ledgerR : LedgerR) → Set
correctTX tr ledgerR = correctInputs (outputs (tx tr)) ledgerR



UnMinedBlock : Set

-- \bitcoinVersFive
UnMinedBlock = List TX


-- \bitcoinVersFive
tx2TXFee : TX → Amount
tx2TXFee tr =
    txFieldList2TotalAmount (outputs (tx tr)) ∸ txFieldList2TotalAmount (inputs (tx tr))

unMinedBlock2TXFee : UnMinedBlock → Amount
unMinedBlock2TXFee bl = sumListViaf tx2TXFee  bl



-- \bitcoinVersFive
correctUnminedBlock : (block : UnMinedBlock)(oldLedgerR : LedgerR)→ Set
correctUnminedBlock [] oldLedgerR = ⊤
correctUnminedBlock (tr ∷ block) oldLedgerR =
    correctTX tr oldLedgerR ×  correctUnminedBlock  block (updateLedgerRByTX tr oldLedgerR)

updateLedgerRUnminedBlock : (block : UnMinedBlock)(oldLedgerR : LedgerR) → LedgerR
updateLedgerRUnminedBlock [] oldLedgerR            = oldLedgerR
updateLedgerRUnminedBlock (tr ∷ block) oldLedgerR  =
        updateLedgerRUnminedBlock block (updateLedgerRByTX tr oldLedgerR)

BlockUnchecked : Set

-- \bitcoinVersFive
BlockUnchecked = List TXField × UnMinedBlock

block2TXFee : BlockUnchecked → Amount
block2TXFee (outputMiner , block) = unMinedBlock2TXFee block

{-
upDateLedgerRMining : (minerOutput  : List TXField)
                     (oldLedgerR : LedgerR)
                     → LedgerR
upDateLedgerRMining minerOutput oldLedgerR =
           addTXFieldListToLedgerR minerOutput oldLedgerR
--              (txField reward miner)
-}

-- \bitcoinVersFive
correctMinedBlock : (reward : Amount)(block : BlockUnchecked)(oldLedgerR : LedgerR)
                    → Set
correctMinedBlock reward (outputMiner , block) oldLedgerR =
      correctUnminedBlock block oldLedgerR ×
      txFieldList2TotalAmount outputMiner ≡ℕ (reward + unMinedBlock2TXFee block)
--          (upDateLedgerRMining reward miner )

-- \bitcoinVersFive
updateLedgerRBlock : (block : BlockUnchecked)(oldLedgerR : LedgerR)→ LedgerR
updateLedgerRBlock (outputMiner , block) oldLedgerR =
   addTXFieldListToLedgerR  outputMiner (updateLedgerRUnminedBlock block oldLedgerR)

-- next blockchain
-- reward can be a function f : Time → Amount

BlockChainUnchecked : Set

-- \bitcoinVersFive
BlockChainUnchecked = List BlockUnchecked

-- \bitcoinVersFive
CorrectBlockChain : (minerReward : Time → Amount)
                    (startTime : Time)
                    (sartLedgerR : LedgerR)
                    (bc  : BlockChainUnchecked)
                    → Set
CorrectBlockChain rewardFun startTime startLedgerR [] = ⊤
CorrectBlockChain rewardFun startTime startLedgerR (block ∷ restbc)
   = correctMinedBlock (rewardFun startTime) block startLedgerR
     ×  CorrectBlockChain rewardFun (suc startTime)
        (updateLedgerRBlock block startLedgerR)  restbc

-- \bitcoinVersFive
FinalLedgerR :  (txFeePrevious : Amount)     (minerReward : Time → Amount)
                (startTime : Time)           (startLedgerR : LedgerR)
                (bc  : BlockChainUnchecked)  → LedgerR
FinalLedgerR trfee rewardFun startTime startLedgerR [] = startLedgerR
FinalLedgerR trfee rewardFun startTime startLedgerR (block ∷ restbc)  =
  FinalLedgerR (block2TXFee block) rewardFun (suc startTime)
     (updateLedgerRBlock block startLedgerR) restbc

-- \bitcoinVersFive
record BlockChain (minerReward : Time → Amount) : Set where
  field  blockchain  : BlockChainUnchecked
         correct     : CorrectBlockChain minerReward 0 initialLedger blockchain

open BlockChain public

blockChain2FinalLedgerR :  (minerReward : Time → Amount)(bc : BlockChain minerReward)
                           → LedgerR
blockChain2FinalLedgerR minerReward bc =
   FinalLedgerR 0 minerReward 0 initialLedger (blockchain bc)
