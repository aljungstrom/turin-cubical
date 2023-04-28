{-# OPTIONS --cubical --safe #-}
module Nat where

open import Primitives

open import Agda.Builtin.Nat public
  using (zero; suc; _+_)
  renaming (Nat to ℕ; _-_ to _∸_; _*_ to _·_)

open import Agda.Builtin.Unit public
  renaming (⊤ to Unit)

open import Agda.Builtin.FromNat public
  renaming (Number to HasFromNat)
open import Agda.Builtin.FromNeg public
  renaming (Negative to HasFromNeg)

-- {-
-- open import Cubical.Data.Bool.Base
-- open import Cubical.Data.Sum.Base hiding (elim)
-- open import Cubical.Data.Empty.Base hiding (elim)
-- open import Cubical.Data.Unit.Base
-- -}

instance
  fromNatℕ : HasFromNat ℕ
  fromNatℕ = record { Constraint = λ _ → Unit ; fromNat = λ n → n }

predℕ : ℕ → ℕ
predℕ zero = 0
predℕ (suc n) = n

caseNat : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS zero    = a0
caseNat a0 aS (suc n) = aS

doubleℕ : ℕ → ℕ
doubleℕ zero = zero
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n · m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ zero m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

-- iterate
iter : ∀ {ℓ} {A : Type ℓ} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)

elim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → A zero
  → ((n : ℕ) → A n → A (suc n))
  → (n : ℕ) → A n
elim a₀ _ zero = a₀
elim a₀ f (suc n) = f n (elim a₀ f n)



-- This is used in prelude to show that ℕ is a set
data ⊥ : Type where

ℕ-fib : (n : ℕ) → Type
ℕ-fib zero = Unit
ℕ-fib (suc n) = ⊥

ℕ-code : (n m : ℕ) → Type
ℕ-code zero zero = Unit
ℕ-code (suc n) zero = ⊥
ℕ-code zero (suc m) = ⊥
ℕ-code (suc n) (suc m) = ℕ-code n m

ℕ-encode-diag : (n : ℕ) → ℕ-code n n
ℕ-encode-diag zero = tt
ℕ-encode-diag (suc n) = ℕ-encode-diag n

ℕ-encode : (n m : ℕ) → (n ≡ m) → ℕ-code n m
ℕ-encode n m p = transp (λ i → ℕ-code n (p i)) i0 (ℕ-encode-diag n)

ℕ-decode : (n m : ℕ) → ℕ-code n m → n ≡ m
ℕ-decode zero zero _ _ = zero
ℕ-decode zero (suc m) ()
ℕ-decode (suc n) zero ()
ℕ-decode (suc n) (suc m) p i = suc (ℕ-decode n m p i)

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero n o _  = n + o
+-assoc (suc m) n o i = suc (+-assoc m n o i)
