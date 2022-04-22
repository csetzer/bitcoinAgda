module libraries.natLib where

open import Data.Nat hiding (_≥_)
open import Data.Bool
open import Data.Unit

_≡ℕb_ : ℕ → ℕ → Bool
zero ≡ℕb zero = true
zero ≡ℕb suc m = false
suc n ≡ℕb zero = false
suc n ≡ℕb suc m = n ≡ℕb m

_≡ℕ_ : ℕ → ℕ → Set
n ≡ℕ m = T (n ≡ℕb m)

_≦b_ : ℕ → ℕ → Bool
zero ≦b n = true
suc n ≦b zero = false
suc n ≦b suc m = n ≦b m

_≦_ : ℕ → ℕ → Set
n  ≦ m = T (n ≦b m)

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≦ n
