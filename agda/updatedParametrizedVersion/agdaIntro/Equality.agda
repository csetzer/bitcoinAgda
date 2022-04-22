{-# OPTIONS --without-K #-}

module agdaIntro.Equality where

infix 4 _≡_

--\EqualityModule
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
