open import basicFunctions

module bitcoinLedgerModel (basicFunctions : BasicFunctions) where

open import libraries.listLib
open import libraries.natLib
open import Data.Nat hiding (_≥_)
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Nat.Base hiding (_≥_)


hashMsg : Msg → ℕ
hashMsg = basicFunctions  .BasicFunctions.hashMsg

publicKey2Address : (pubk : PublicKey) → Address
publicKey2Address = basicFunctions .BasicFunctions.publicKey2Address


Signed : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set
Signed = basicFunctions .BasicFunctions.Signed

blockReward : Time → Amount
blockReward  = basicFunctions .BasicFunctions.blockReward


record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
  constructor signedWithSigPbk
  field  publicKey  :  PublicKey
         pbkCorrect :  publicKey2Address publicKey ≡ℕ  address
         signature  :  Signature
         signed     :  Signed msg publicKey signature
open SignedWithSigPbk public


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
  constructor txUnsigned
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
tx2Signaux []               outp  = ⊤
tx2Signaux (inp ∷ restinp)  outp  =
    SignedWithSigPbk (txInput2Msg inp outp) (address inp) ×  tx2Signaux restinp outp

tx2Sign : TXUnsigned → Set
tx2Sign tr = tx2Signaux (inputs tr) (outputs tr)


-- \bitcoinVersFive
record TX : Set where
  constructor txc
  field  tx       :  TXUnsigned
         cor      : txFieldList2TotalAmount (inputs tx) ≥ txFieldList2TotalAmount (outputs tx)
         nonEmpt  : NonNil (inputs tx) × NonNil (outputs tx)
         sig      : tx2Sign tx

open TX public

Ledger : Set

-- \bitcoinVersFive
Ledger = (addr : Address) → Amount

initialLedger : Ledger
initialLedger addr = 0

-- \bitcoinVersFive
addTXFieldToLedger :  (tr : TXField)(oldLedger : Ledger) → Ledger
addTXFieldToLedger  tr oldLedger pubk =
         if   pubk ≡ℕb address tr then oldLedger pubk +  amount tr else oldLedger pubk

addTXFieldListToLedger  :  (tr : List TXField)(oldLedger : Ledger) → Ledger
addTXFieldListToLedger []        oldLedger  =  oldLedger
addTXFieldListToLedger (x ∷ tr)  oldLedger  =
      addTXFieldListToLedger tr (addTXFieldToLedger x oldLedger)


-- \bitcoinVersFive
subtrTXFieldFromLedger      :  (tr : TXField)       (oldLedger : Ledger)  →  Ledger
subtrTXFieldListFromLedger  :  (tr : List TXField)  (oldLedger : Ledger)  →  Ledger
subtrTXFieldFromLedger  tr oldLedger pubk =
         if   pubk ≡ℕb address tr
         then oldLedger pubk ∸  amount tr
         else oldLedger pubk

subtrTXFieldListFromLedger [] oldLedger = oldLedger
subtrTXFieldListFromLedger (x ∷ tr) oldLedger =
           subtrTXFieldListFromLedger tr (subtrTXFieldFromLedger x oldLedger)

-- \bitcoinVersFive
updateLedgerByTX :  (tr : TX)(oldLedger : Ledger) → Ledger
updateLedgerByTX tr oldLedger =  addTXFieldListToLedger (outputs (tx tr))
                                   (subtrTXFieldListFromLedger (inputs (tx tr)) oldLedger )


-- \bitcoinVersFive
correctInput : (tr : TXField) (ledger : Ledger) → Set
correctInput tr ledger = ledger (address tr) ≥ amount tr

-- \bitcoinVersFive
correctInputs : (tr : List TXField) (ledger : Ledger) → Set
correctInputs []        ledger  = ⊤
correctInputs (x ∷ tr)  ledger  = correctInput x ledger ×
                                  correctInputs tr (subtrTXFieldFromLedger x ledger)

correctTX : (tr : TX) (ledger : Ledger) → Set
correctTX tr ledger = correctInputs (inputs (tx tr)) ledger



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
correctUnminedBlock : (block : UnMinedBlock)(oldLedger : Ledger)→ Set
correctUnminedBlock  []            oldLedger  = ⊤
correctUnminedBlock  (tr ∷ block)  oldLedger  =
    correctTX tr oldLedger ×  correctUnminedBlock  block (updateLedgerByTX tr oldLedger)

updateLedgerUnminedBlock : (block : UnMinedBlock)(oldLedger : Ledger) → Ledger
updateLedgerUnminedBlock []            oldLedger  = oldLedger
updateLedgerUnminedBlock (tr ∷ block)  oldLedger  =
    updateLedgerUnminedBlock block (updateLedgerByTX tr oldLedger)

BlockUnchecked : Set

-- \bitcoinVersFive
BlockUnchecked = List TXField × UnMinedBlock

block2TXFee : BlockUnchecked → Amount
block2TXFee (outputMiner , block) = unMinedBlock2TXFee block

{-
upDateLedgerMining : (minerOutput  : List TXField)
                     (oldLedger : Ledger)
                     → Ledger
upDateLedgerMining minerOutput oldLedger =
           addTXFieldListToLedger minerOutput oldLedger
--              (txField reward miner)
-}

-- \bitcoinVersFive
correctMinedBlock : (reward : Amount)(block : BlockUnchecked)(oldLedger : Ledger) → Set

correctMinedBlock reward (outputMiner , block) oldLedger =
      correctUnminedBlock block oldLedger ×
      txFieldList2TotalAmount outputMiner ≡ℕ (reward + unMinedBlock2TXFee block)
--          (upDateLedgerMining reward miner )

-- \bitcoinVersFive
updateLedgerBlock : (block : BlockUnchecked)(oldLedger : Ledger)→ Ledger
updateLedgerBlock (outputMiner , block) oldLedger =
   addTXFieldListToLedger  outputMiner (updateLedgerUnminedBlock block oldLedger)

-- next blockchain
-- reward can be a function f : Time → Amount

BlockChainUnchecked : Set

-- \bitcoinVersFive
BlockChainUnchecked = List BlockUnchecked

-- \bitcoinVersFive
CorrectBlockChain : (startTime : Time)
                    (sartLedger : Ledger)
                    (bc  : BlockChainUnchecked)
                    → Set
CorrectBlockChain startTime startLedger [] = ⊤
CorrectBlockChain startTime startLedger (block ∷ restbc)
   = correctMinedBlock (blockReward startTime) block startLedger
     ×  CorrectBlockChain (suc startTime)
        (updateLedgerBlock block startLedger)  restbc

-- \bitcoinVersFive
FinalLedger :  (txFeePrevious : Amount)
                (startTime : Time)           (startLedger : Ledger)
                (bc  : BlockChainUnchecked)  → Ledger
FinalLedger trfee startTime startLedger [] = startLedger
FinalLedger trfee startTime startLedger (block ∷ restbc)  =
  FinalLedger (block2TXFee block) (suc startTime)
     (updateLedgerBlock block startLedger) restbc

-- \bitcoinVersFive
record BlockChain : Set where
  constructor blockchainc
  field  blockchain  : BlockChainUnchecked
         correct     : CorrectBlockChain 0 initialLedger blockchain

open BlockChain public

blockChain2FinalLedger :  (bc : BlockChain) → Ledger
blockChain2FinalLedger bc =
   FinalLedger 0 0 initialLedger (blockchain bc)
