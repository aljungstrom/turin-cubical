{-# OPTIONS #-}

module ListBin where

open import prelude hiding (transport ; J)
open import Nat
open import IsoToEquiv hiding (fiber ; _≃_ ; isEquiv) 

data Bool : Type where
  false : Bool
  true : Bool 

data ListBin : Type where -- binary numbers 'backwards', i.e. 110 denotes 2^0 + 2^1 + 0*(2^2)
  []    : ListBin
  _∷_   : (x : Bool) (xs : ListBin) → ListBin
  drop0 : false ∷ [] ≡ []

-- 1 as a binary number
1LB : ListBin
1LB = true ∷ []

sucListBin : ListBin → ListBin
sucListBin [] = 1LB
sucListBin (true ∷ xs) = false ∷ sucListBin xs
sucListBin (false ∷ xs) = true ∷ xs
sucListBin (drop0 i) = 1LB

_+LB_ : ListBin → ListBin → ListBin
rUnit+LB : (x : ListBin) → x +LB [] ≡ x
[] +LB y = y
(x ∷ xs) +LB [] = x ∷ xs
(true ∷ xs) +LB (true ∷ ys) = false ∷ sucListBin (xs +LB ys)
(true ∷ xs) +LB (false ∷ ys) = true ∷ (xs +LB ys)
(false ∷ xs) +LB (y ∷ ys) = y ∷ (xs +LB ys)
(true ∷ xs) +LB drop0 i = true ∷ (rUnit+LB xs i)
(false ∷ xs) +LB drop0 i = false ∷ (rUnit+LB xs i)
drop0 i +LB [] = drop0 i
drop0 i +LB (y ∷ ys) = y ∷ ys
drop0 i +LB drop0 j = drop0 (j ∧ i)
rUnit+LB [] = refl _
rUnit+LB (x ∷ x₁) = refl _
rUnit+LB (drop0 i) = refl _


ListBin→ℕ : ListBin → ℕ
ListBin→ℕ [] = 0
ListBin→ℕ (true ∷ xs) = suc (2 · ListBin→ℕ xs)
ListBin→ℕ (false ∷ xs) = 2 · ListBin→ℕ xs
ListBin→ℕ (drop0 i) = 0

sucListBinDistrL : (x y : ListBin) → sucListBin (x +LB y) ≡ (sucListBin x +LB y)
sucListBinDistrL [] [] = refl _
sucListBinDistrL [] (true ∷ y) = refl _
sucListBinDistrL [] (false ∷ y) = refl _
sucListBinDistrL [] (drop0 i) = refl _
sucListBinDistrL (true ∷ xs) [] = refl _
sucListBinDistrL (false ∷ xs) [] = refl _
sucListBinDistrL (true ∷ xs) (true ∷ y) = ap (true ∷_) (sucListBinDistrL xs y)
sucListBinDistrL (true ∷ xs) (false ∷ y) = ap (false ∷_) (sucListBinDistrL xs y)
sucListBinDistrL (false ∷ xs) (true ∷ y) = refl _
sucListBinDistrL (false ∷ xs) (false ∷ y) = refl _ 
sucListBinDistrL (true ∷ []) (drop0 i)  = refl _
sucListBinDistrL (true ∷ (true ∷ xs)) (drop0 i) = refl _
sucListBinDistrL (true ∷ (false ∷ xs)) (drop0 i) = refl _
sucListBinDistrL (true ∷ drop0 i) (drop0 j) = refl _ 
sucListBinDistrL (false ∷ xs) (drop0 i) = refl _
sucListBinDistrL (drop0 i) [] = refl _
sucListBinDistrL (drop0 i) (true ∷ y) = refl _
sucListBinDistrL (drop0 i) (false ∷ y) = refl _
sucListBinDistrL (drop0 i) (drop0 j) = refl _

ℕ→ListBin : ℕ → ListBin
ℕ→ListBin zero = []
ℕ→ListBin (suc x) = sucListBin (ℕ→ListBin x)

ℕ→ListBin-pres+ : (x y : ℕ) → ℕ→ListBin (x + y) ≡ (ℕ→ListBin x +LB ℕ→ListBin y)
ℕ→ListBin-pres+ zero y = refl _
ℕ→ListBin-pres+ (suc x) zero =
  ap sucListBin (ap ℕ→ListBin (+-comm x zero))
  ∙ sym (rUnit+LB (sucListBin (ℕ→ListBin x)))
ℕ→ListBin-pres+ (suc x) (suc y) =
  ap sucListBin (ℕ→ListBin-pres+ x (suc y))
   ∙ sucListBinDistrL (ℕ→ListBin x) (sucListBin (ℕ→ListBin y))


postulate
  maps-cancel-l : (x : ℕ) → ListBin→ℕ (ℕ→ListBin x) ≡ x
  maps-cancel-r : (y : ListBin) → ℕ→ListBin (ListBin→ℕ y) ≡ y
