module libraries.natLib where

open import Data.Nat
open import Data.Bool
open import Data.Unit

_≡ℕb_ : ℕ → ℕ → Bool
zero ≡ℕb zero = true
zero ≡ℕb suc m = false
suc n ≡ℕb zero = false
suc n ≡ℕb suc m = n ≡ℕb m

_≡ℕ_ : ℕ → ℕ → Set
n ≡ℕ m = T (n ≡ℕb m)
