{-# OPTIONS --cubical #-}

module IsoToEquiv where

open import prelude
open import Nat

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

-- equivalences
fiber : (f : A → B) (b : B) → Type _
fiber {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)

isEquiv : (f : A → B) → Type _
isEquiv { B = B} f = (b : B) → isContr (fiber f b)

_≃_  : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B  = Σ[ f ∈ (A → B) ] (isEquiv f)

invEq : A ≃ B → B → A
invEq e b = e .snd b .fst .fst

retEq : (e : A ≃ B) → (a : A) → (invEq e (fst e a)) ≡ a
retEq e a i = e .snd (fst e a) .snd (a , λ _ → fst e a) i .fst

secEq : (e : A ≃ B) → (b : B) → fst e (invEq e b) ≡ b
secEq e b = e .snd b .fst .snd


-- identity equivalence
idEquiv : (A : Type ℓ) → A ≃ A
fst (idEquiv A) x = x
fst (fst (snd (idEquiv A) a)) = a
snd (fst (snd (idEquiv A) a)) _ = a
fst (snd (snd (idEquiv A) a) (a' , q) i) = q (~ i)
snd (snd (snd (idEquiv A) a) (a' , q) i) t = q (t ∨ ~ i)


-- isos
record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : (x : _) → fun (inv x) ≡ x
    leftInv  : (x : _) → inv (fun x) ≡ x

-- Any iso is an equivalence
module _ {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  fst (fst (isoToIsEquiv y)) = g y
  snd (fst (isoToIsEquiv y)) = s y
  snd (isoToIsEquiv y) z = lemIso y (g y) (fst z) (s y) (snd z)

isoToEquiv : Iso A B → A ≃ B
isoToEquiv i .fst = i .Iso.fun
isoToEquiv i .snd = isoToIsEquiv i

-- Glue (used for univalence)
Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → (fst (Te x .snd))
                          ,  record { equiv-proof = λ y → snd (Te x .snd) y })
