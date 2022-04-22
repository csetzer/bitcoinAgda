module agdaIntro.finn where

open import Data.Nat
open import Data.Empty

--\lagdaFinn
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

--\lagdaFinn
mutual
  data Even : ℕ → Set where
    0p    : Even 0
    sucp  : {n : ℕ}  →  Odd n   →  Even  (suc  n)

  data Odd : ℕ → Set where
    sucp  : {n : ℕ}  →  Even n  →  Odd   (suc  n)

--\lagdaFinn
postulate nonExistentElement : Fin 0
