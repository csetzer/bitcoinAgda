module basicFunctions where

open import Data.Nat hiding (_≥_)
open import Data.List
open import libraries.natLib

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





record BasicFunctions : Set₁ where
  field
     hashMsg : Msg → ℕ
-- \bitcoinVersFive
     publicKey2Address : (pubk : PublicKey) → Address
    -- Signed means that Msg msg has been signed
     -- by private key corresponding to pubk
     Signed : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set
     blockReward : Time → Amount
