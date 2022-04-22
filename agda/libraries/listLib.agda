module libraries.listLib where

open import Data.List
open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Unit.Base
open import Function
open import Relation.Binary.PropositionalEquality


mapL : {X Y : Set}(f : X → Y)(l : List X) → List Y
mapL f []       = []
mapL f (x ∷ l)  = f x ∷ mapL f l

corLengthMapL : {X Y : Set}(f : X → Y)(l : List X) → length (mapL f l) ≡ length l
corLengthMapL f [] = refl
corLengthMapL f (x ∷ l) = cong suc (corLengthMapL f  l)



nth : {X : Set}(l : List X) (i : Fin (length l)) → X
nth [] ()
nth (x ∷ l) zero = x
nth (x ∷ l) (suc i) = nth l i

delFromList : {X : Set}(l : List X)(i : Fin (length l)) → List X
delFromList [] ()
delFromList (x ∷ l) zero = l
delFromList (x ∷ l) (suc i) = x ∷ delFromList l i

-- an index of (delFromList l i) is mapped to an index of l
delFromListIndexToOrigIndex : {X : Set}(l : List X)(i : Fin (length l))
                                   (j : Fin (length (delFromList l i)))
                                   → Fin (length l)
delFromListIndexToOrigIndex [] () j
delFromListIndexToOrigIndex (x ∷ l) zero j = suc j
delFromListIndexToOrigIndex (x ∷ l) (suc i) zero = zero
delFromListIndexToOrigIndex (x ∷ l) (suc i) (suc j) = suc (delFromListIndexToOrigIndex l i j)

correctNthDelFromList : {X : Set}(l : List X)(i : Fin (length l))
                        (j : Fin (length (delFromList l i)))
                        → nth (delFromList l i) j ≡ nth l (delFromListIndexToOrigIndex l i j)
correctNthDelFromList [] () j
correctNthDelFromList (x ∷ l) zero j = refl
correctNthDelFromList (x ∷ l) (suc i) zero = refl
correctNthDelFromList (x ∷ l) (suc i) (suc j) = correctNthDelFromList l i j

--\listLib
concatListIndex2OriginIndices : {X Y : Set}(l l' : List X)
                                (f   :  Fin (length l) → Y)(f'  :  Fin (length l') → Y)
                                (i   : Fin (length (l ++ l')))  → Y
concatListIndex2OriginIndices [] l' f f' i = f' i
concatListIndex2OriginIndices (x ∷ l) l' f f' zero = f zero
concatListIndex2OriginIndices (x ∷ l) l' f f' (suc i) =
         concatListIndex2OriginIndices l l' (f ∘ suc) f' i


corCconcatListIndex2OriginIndices : {X Y : Set}(l l' : List X)
                                    (f : X → Y)
                                    (g : Fin (length l) → Y)
                                    (g' : Fin (length l') → Y)
                                    (cor1 : (i : Fin (length l)) → f (nth l i) ≡ g i)
                                    (cor2 : (i' : Fin (length l')) → f (nth l' i') ≡ g' i')
                                    (i : Fin (length (l ++ l')))
                                    → f (nth (l ++ l') i)
                                       ≡ concatListIndex2OriginIndices l l' g g' i
corCconcatListIndex2OriginIndices [] l' f g g' cor1 cor2 i = cor2 i
corCconcatListIndex2OriginIndices (x ∷ l) l' f g g' cor1 cor2 zero = cor1 zero
corCconcatListIndex2OriginIndices (x ∷ l) l' f g g' cor1 cor2 (suc i) =
    corCconcatListIndex2OriginIndices l l' f (g ∘ suc) g' (cor1 ∘ suc) cor2 i


--\listLib
listOfElementsOfFin : (n : ℕ) → List (Fin n)
listOfElementsOfFin zero = []
listOfElementsOfFin (suc n) = zero ∷ (mapL suc (listOfElementsOfFin n))

corListOfElementsOfFinLength : (n : ℕ) → length (listOfElementsOfFin n) ≡ n
corListOfElementsOfFinLength zero = refl
corListOfElementsOfFinLength (suc n) = cong suc cor3
    where
         cor1 : length (mapL {Y = Fin (suc n)} (λ i → suc i) (listOfElementsOfFin n)) ≡ length (listOfElementsOfFin n)
         cor1 = corLengthMapL suc (listOfElementsOfFin n)

         cor2 : length (listOfElementsOfFin n) ≡ n
         cor2 = corListOfElementsOfFinLength n

         cor3 : length (mapL {Y = Fin (suc n)} (λ i → suc i) (listOfElementsOfFin n)) ≡ n
         cor3 = trans cor1 cor2

-- subtract list consists of elements from the list which are about to
-- be subtracted from it.
-- every element of the list can be subtracted only once
-- however since elements can occur multiple times they can still occur
-- multiple times (as many times as they occur in the list) from the list

--\listLib
data SubList {X : Set} : (l : List X) → Set where
  []    :  {l : List X} → SubList l
  cons  :  {l : List X}(i : Fin (length l))(o : SubList (delFromList l i)) → SubList l

--\listLib
listMinusSubList : {X : Set}(l : List X)(o : SubList l) → List X
listMinusSubList l []          = l
listMinusSubList l (cons i o)  = listMinusSubList (delFromList l i) o

subList2List : {X : Set}{l : List X}(sl : SubList l) → List X
subList2List []                   = []
subList2List {l = l} (cons i sl)  = nth l i ∷ subList2List sl

--\listLib
data SubList+ {X : Set} (Y : Set) : (l : List X) → Set where
  []   :  {l : List X} → SubList+ Y l
  cons :  {l : List X}(i : Fin (length l))(y : Y)(o : SubList+ Y (delFromList l i))
          → SubList+ Y l

--\listLib
listMinusSubList+ : {X Y : Set}(l : List X)(o : SubList+ Y l) → List X

listMinusSubList+ l [] = l
listMinusSubList+ l (cons i y o) = listMinusSubList+ (delFromList l i) o


-- needed fromutxo2Msg
--\listLib
subList+2List : {X Y : Set}{l : List X}(sl : SubList+ Y l) → List (X × Y)

subList+2List [] = []
subList+2List {X} {Y} {l} (cons i y sl) = (nth l i , y) ∷ subList+2List sl

--\listLib
listMinusSubList+Index2OrgIndex : {X Y : Set}(l : List X)(o : SubList+ Y l)
                                  (i : Fin (length (listMinusSubList+ l o))) → Fin (length l)

listMinusSubList+Index2OrgIndex l [] i              = i
listMinusSubList+Index2OrgIndex l (cons i₁ y o) i   =
         delFromListIndexToOrigIndex l i₁ (listMinusSubList+Index2OrgIndex (delFromList l i₁) o i)

corListMinusSubList+Index2OrgIndex : {X Y : Set}(l : List X)(o : SubList+ Y l)
                                  (i : Fin (length (listMinusSubList+ l o)))
                                  → nth (listMinusSubList+ l o) i
                                      ≡ nth l (listMinusSubList+Index2OrgIndex l o i)
corListMinusSubList+Index2OrgIndex l [] i = refl
corListMinusSubList+Index2OrgIndex [] (cons () y o) i
corListMinusSubList+Index2OrgIndex (x ∷ l) (cons zero y o) i = corListMinusSubList+Index2OrgIndex l o i
corListMinusSubList+Index2OrgIndex (x ∷ l) (cons (suc i₁) y o) i = trans eq1 eq2
      where
         eq1 : nth (listMinusSubList+ (x ∷ delFromList l i₁) o) i ≡
               nth (x ∷ delFromList l i₁)
                  (listMinusSubList+Index2OrgIndex (x ∷ delFromList l i₁) o i)
         eq1 = corListMinusSubList+Index2OrgIndex (x ∷ delFromList l i₁) o i

         eq2 : nth (x ∷ delFromList l i₁)
                  (listMinusSubList+Index2OrgIndex (x ∷ delFromList l i₁) o i)
               ≡ nth (x ∷ l)
                  (delFromListIndexToOrigIndex (x ∷ l) (suc i₁)
                  (listMinusSubList+Index2OrgIndex (x ∷ delFromList l i₁) o i))
         eq2  = correctNthDelFromList (x ∷ l) (suc i₁)
                ((listMinusSubList+Index2OrgIndex (x ∷ delFromList l i₁) o i))


--\listLib
subList+2IndicesOriginalList : {X Y : Set}(l : List X)(sl : SubList+ Y l) → List (Fin (length l) × Y)
subList+2IndicesOriginalList l [] = []
subList+2IndicesOriginalList {X} {Y} l (cons i y sl) =
      (i , y) ∷ mapL (λ{(j , y) → (delFromListIndexToOrigIndex l i j , y)}) res1
    where
        res1 : List (Fin (length (delFromList l i)) × Y)
        res1 = subList+2IndicesOriginalList (delFromList l i) sl


-- \listLib
sumListViaf : {X : Set} (f : X → ℕ)(l : List X) → ℕ
sumListViaf f [] = 0
sumListViaf f (x ∷ l) = f x + sumListViaf f l

--\listLib
∀inList : {X : Set}(l : List X)(P : X → Set) → Set
∀inList [] P        = ⊤
∀inList (x ∷ l) P   = P x ×  ∀inList l  P

--\listLib
nonNil : {X : Set}(l : List X) → Bool
nonNil [] = false
nonNil (_ ∷ _) = true

NonNil : {X : Set}(l : List X) → Set
NonNil l = T (nonNil l)


-- adds the index to it but adds in addition n to the result
-- used as an auxiliary function in the next part

list2ListWithIndexaux : {X : Set}(n : ℕ) (l : List X) → List (X × ℕ)
list2ListWithIndexaux n [] = []
list2ListWithIndexaux n (x ∷ l) = (x , n) ∷ list2ListWithIndexaux (suc n) l

list2ListWithIndex : {X : Set}(l : List X) → List (X × ℕ)
list2ListWithIndex l = list2ListWithIndexaux 0 l
