{-# OPTIONS --cubical #-}

module cprelude where

open import Primitives public
open import Nat public

{-
infixr 30 _∙_
infixr 30 _∙₂_
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infixr 2.5 _≡⟨_⟩≡⟨_⟩_
infixl 4 _≡$_ _≡$S_
-}

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

J : {x : A} (P : (y : A) → x ≡ y → Type ℓ) (d : P x (λ _ → x))
    {y : A} (p : x ≡ y) → P y p
J P d p = transp (λ i → P (p i) λ j → p (i ∧ j)) i0 d

-- hlevels
isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isGroupoid : Type ℓ → Type ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

-- path composition
compPath-filler : {x y z : A} → x ≡ y → y ≡ z → I → I → A
compPath-filler {x = x} p q j i =
  hfill (λ j → λ {(i = i0) → x
                 ; (i = i1) → q j})
        (inS (p i))
        j

_∙_ : x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = compPath-filler p q i1 i

sym : x ≡ y → y ≡ x
sym p i = p (~ i)

rUnit : (p : x ≡ y) → p ∙ (λ _ → y) ≡ p
rUnit {y = y} p i j = compPath-filler p (λ _ → y) (~ i) j

rCancel : (p : x ≡ y) → p ∙ sym p ≡ λ _ → x
rCancel {x = x} {y = y} p i j = 
  hcomp (λ k → λ {(i = i0) → compPath-filler p (sym p) k j
                 ; (i = i1) → p (~ k ∧ j)
                 ; (j = i0) → x
                 ; (j = i1) → p (~ k)})
        (p j)

lCancel : (p : x ≡ y) → sym p ∙ p ≡ λ _ → y
lCancel p = rCancel (sym p)

-- more hlevels
isPropIsContr : isProp (isContr A)
fst (isPropIsContr p q i) = snd p (fst q) i
snd (isPropIsContr p q i) a j =
  hcomp (λ k → λ {(i = i0) → snd p a j
                 ; (i = i1) → snd p (snd q a j) k
                 ; (j = i0) → snd p (snd q a j) (i ∧ k)
                 ; (j = i1) → snd p a (k ∨ ~ i)})
        (snd p a (~ i ∧ j))

isOfHLevelRetract :
  (n : ℕ) {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) (g : B → A)
  → ((x : _) → f (g x) ≡ x)
  → isOfHLevel n A
  → isOfHLevel n B
isOfHLevelRetract zero f g p hlev =
  (f (hlev .fst))
  , λ b → (λ i → f (hlev .snd (g b) i))
         ∙ p b
isOfHLevelRetract (suc zero) f g p hlev x y =
  sym (p x) ∙ ((λ i → f (hlev (g x) (g y) i)) ∙ p y)
isOfHLevelRetract (suc (suc n)) f g p hlev x y =
  isOfHLevelRetract (suc n) {A = g x ≡ g y}
    (λ q → (sym (p x) ∙ (λ i → f (q i))) ∙ p y) (λ q i → g (q i))
      (J (λ y t → ((sym (p x) ∙ (λ i → f (g (t i)))) ∙ p y) ≡ t)
          ((λ i → rUnit (sym (p x)) i ∙ p x)
         ∙ lCancel (p x)))
      (hlev _ _)

isOfHLevelΠ : (n : ℕ) → {A : Type ℓ} {B : A → Type ℓ'}
  → ((x : A) → isOfHLevel n (B x))
  → isOfHLevel n ((x : A) → B x)
fst (isOfHLevelΠ zero h) x = fst (h x)
snd (isOfHLevelΠ zero h) f i x = snd (h x) (f x) i
isOfHLevelΠ (suc zero) h f g i x = h x (f x) (g x) i
isOfHLevelΠ (suc (suc n)) h f g =
  isOfHLevelRetract (suc n) {A = ((x : _) → f x ≡ g x)}
    (λ h i x → h x i)
    (λ p x i → p i x)
    (λ t i → t)
    (isOfHLevelΠ (suc n) λ x → h x (f x) (g x))

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

isPropIsOfHLevel : (n : ℕ) → isProp (isOfHLevel n A)
isPropIsOfHLevel zero = isPropIsContr
isPropIsOfHLevel (suc zero) p q i =
  fst (isPropIsContr
       (p , λ s i x y → isProp→isSet p _ _ (p x y) (s x y) i)
       (q , λ s i x y → isProp→isSet q _ _ (q x y) (s x y) i) i)
isPropIsOfHLevel (suc (suc n)) =
  isOfHLevelΠ 1 λ x → isOfHLevelΠ 1 λ y
    → isPropIsOfHLevel (suc n)

isSetℕ : isSet ℕ
isSetℕ n m =
  isOfHLevelRetract 1
    (ℕ-decode n m)
    (ℕ-encode n m)
    (ℕ-encode-decode n m )
    (help n m)
    where
    ℕ-encode-decode : (n m : ℕ) → (p : n ≡ m) → ℕ-decode n m (ℕ-encode n m p) ≡ p
    ℕ-encode-decode n m =
      J (λ m p → ℕ-decode n m (ℕ-encode n m p) ≡ p)
        ((λ i → ℕ-decode n n (transp (λ _ → ℕ-code n n) i (ℕ-encode-diag n)))
                ∙ main n)
      where
      main : (n : ℕ) → ℕ-decode n n (ℕ-encode-diag n) ≡ (λ _ → n)
      main zero _ _ = zero
      main (suc n) j i = suc (main n j i)

    help : (n m : ℕ) → isProp (ℕ-code n m)
    help zero zero tt tt _ = tt
    help zero (suc m) ()
    help (suc n) zero ()
    help (suc n) (suc m) = help n m

-- dependent paths
transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p x = transp (λ i → p i) i0 x

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP : transport (λ i → A i) x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x
                               ; (i = i1) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transport (λ i → A i) x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

  -- right unit lawc


-- open import Cubical.Foundations.Prelude using (_∙_) public

isOfHLevelSuc : (n : ℕ) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc zero h a b = sym (h .snd a) ∙ h .snd b
isOfHLevelSuc (suc zero) h x y p q i j =
  hcomp (λ k → λ {(i = i0) → h (q j) (p j) k
                 ; (i = i1) → h (q j) (q j) k
                 ; (j = i0) → h x x k
                 ; (j = i1) → h y y k})
        (q j)
isOfHLevelSuc (suc (suc n)) h x y = isOfHLevelSuc (suc n) (h x y)

isOfHLevelPath : (n : ℕ) (A : Type ℓ) → isOfHLevel n A → (x y : A) → isOfHLevel (predℕ n) (x ≡ y)
fst (isOfHLevelPath zero A h x y) = sym (h .snd x) ∙ h .snd y
snd (isOfHLevelPath zero A h x y) t i j =
  hcomp (λ k → λ {(i = i0) → (sym (h .snd x) ∙ h .snd (t k)) j
                 ; (i = i1) → t (k ∧ j)
                 ; (j = i0) → x
                 ; (j = i1) → t k})
        (lCancel (h .snd x) i j)
fst (isOfHLevelPath (suc zero) A h x y) = h x y
snd (isOfHLevelPath (suc zero) A h x y) t = isOfHLevelSuc 0 (isOfHLevelPath zero A (x , h _) x y) _ _
isOfHLevelPath (suc (suc n)) A h x y = h x y

PathP≡Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transp (λ j → P (i ∧ j)) (~ i) p) q

isOfHLevelPathP : (n : ℕ) { B : I → Type ℓ}
  → (isOfHLevel n (B i1))
  → (x : _) (y : _)
  → isOfHLevel (predℕ n) (PathP (λ i → B i) x y)
isOfHLevelPathP zero {B = B} hl x y =
  transport (λ i → isContr (PathP≡Path B x y (~ i))) (isOfHLevelPath 0 _ hl _ _)
isOfHLevelPathP (suc n) {B = B} hl x y =
  transport (λ i → isOfHLevel n (PathP≡Path B x y (~ i))) (isOfHLevelPath (suc n) _ hl _ _)


-- List
data List (A : Type ℓ) : Type ℓ where
  [] : List A
  _∷_ : List A → A → List A


-- products
_×_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ[ x ∈ A ] B

-- function composition
_∘_ : {B : Type ℓ} {C : Type ℓ'} (g : B → C) (f : A → B)
  → A → C
(g ∘ f) x = g (f x)
