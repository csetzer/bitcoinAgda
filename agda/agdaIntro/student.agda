module agdaIntro.student where

open import Data.Nat
open import Data.String

--\student
record Student : Set where
  constructor student
  field  name    : String
         studnr  : ℕ
open Student public

exampleStudent : Student
--\student
exampleStudent = student "John" 123456

john : String
--\student
john = exampleStudent .name

--\student
postulate hypotheticalStudent : Student
