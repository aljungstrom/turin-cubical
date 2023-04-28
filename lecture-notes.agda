{-# OPTIONS #-}

module lecture-notes where

open import prelude public hiding (transport ; J)
open import Nat
open import IsoToEquiv hiding (fiber ; _≃_ ; isEquiv) 

infix 10 _⁻

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
    C : A → Type ℓ
    x y z w : A

-- Cubical Agda
-- Libraries: agda/cubical, 1lab

-- Part 1 (Paths)

-- No inductive identity type. Instead _≡_ is described using functions out of an interval I

-- Two endpoints points, i0 i1 : I.

-- (f : I → A) ~ (f i0 ≡ f i1)

-- The followin function returns x
apply₀ : (x y : A) (p : x ≡ y) → A
apply₀ x y p = p i0

-- and this one returns y
apply₁ : (x y : A) (p : x ≡ y) → A
apply₁ x y p = p i1

-- The contant path is the constant functions I → A.
refl : (x : A) → x ≡ x 
refl x = λ i → x


-- function application preserves path composition≃
ap : {x y : A} (f : A → B) (p : x ≡ y) → f x ≡ f y
ap f p i = f (p i)

-- function extensionality is trivial!
funExt : {f g : (x : A) → C x} → ((x : A) → f x ≡ g x) → f ≡ g
-- have : A → (I → B),
-- want : I → (A → B)
funExt h i x = h x i

-- Interval manipulation
-- Minimum _∧_ : I → I → I
-- Maximum _∨_ : I → I → I
-- Symmetry/reversal ~_ : I → I

_⁻ : {x y : A} → x ≡ y → y ≡ x
(p ⁻) i = p (~ i)

-- Dependent paths
-- _≡_ is a special case of a dependent path type
-- Given A : I → Type and points (x₀ : A i0), (x₁ : A i1)
-- in

apd : {x y : A} (f : (x : A) → C x) (p : x ≡ y)
  → PathP (λ i → C (p i)) (f x) (f y)
apd f p i = f (p i)

-- Higher inductive types

data ℤ : Type where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  0≡-0 : pos 0 ≡ neg 0

-_ : ℤ → ℤ
- pos x = neg x
- neg x = pos x
- 0≡-0 i = 0≡-0 (~ i)

-- the circle

data S¹ : Type where
  base : S¹
  loop : base ≡ base

negS¹ : S¹ → S¹
negS¹ base = base
negS¹ (loop i) = loop (~ i)

-- Set quotients
data _/_ (A : Type) (R : A → A → Type) : Type where
  [_] : A → A / R
  eq/ : (x y : A) → R x y → [ x ] ≡ [ y ]
  -- Uh oh...
  trunc : isSet (A / R)

-- trunc is needed.
-- Without trunc Unit / Total != The point but S¹...

-- Annoying. Need to consider an extra case even when mapping into other sets.

-- Solution - write down an explicit eliminator once and for all
/elimSet : {A : Type} {R : A → A → Type}
  → {B : A / R → Type}
  → ((x : A / R) → isSet (B x))
  → ([_]' : (a : A) → B [ a ])
  → (eq/' : (x y : A) (r : R x y) → PathP (λ i → B (eq/ x y r i)) [ x ]' [ y ]')
  → (x : A / R) → B x
/elimSet is-set [_]' eq/' [ x ] = [ x ]'
/elimSet is-set [_]' eq/' (eq/ x y r i) = eq/' x y r i
/elimSet {B = B} is-set [_]' eq/' (trunc x y p q i j) = goal i j
  where
  goal : PathP (λ i → PathP (λ j → (B (trunc x y p q i j)))
                             (/elimSet is-set [_]' eq/' x)
                             (/elimSet is-set [_]' eq/' y))
               (λ j → /elimSet is-set [_]' eq/' (p j))
                λ j → /elimSet is-set [_]' eq/' (q j)
  goal = isOfHLevelPathP 1 (λ _ → isOfHLevelPathP 2  (is-set _)  _ _ _) _ _ .fst

-- When eliminatin into a prop, even fewer cases need checked 
/elimProp : {A : Type} {R : A → A → Type}
  → {B : A / R → Type}
  → ((x : A / R) → isProp (B x))
  → ([_]' : (a : A) → B [ a ])
  → (x : A / R) → B x
/elimProp {B = B} is-prop [_]' =
  /elimSet
    (λ x → isOfHLevelSuc 1 (is-prop x))
    [_]'
    λ x y r → isOfHLevelPathP 1 (is-prop [ y ]) _ _ .fst

-- Example: another version of ℤ
-- idea: represent x : ℤ by pair of nats (n,m) s.t. n - m = x
-- and quotient out

ℤ'-rel : ℕ × ℕ → ℕ × ℕ → Type
ℤ'-rel (a , b) (c , d) = (a + c ≡ b + d)

ℤ' : Type
ℤ' = (ℕ × ℕ) / ℤ'-rel

-- Let's use our elimination principle to define inversion
-ℤ' : ℤ' → ℤ'
-ℤ' = /elimSet (λ _ → trunc)
        (λ {(n , m) → [ m , n ]})
        (λ x y r → eq/ _ _ (sym r))

-- and prove its ivolutive
-ℤ'-invol : (x : ℤ') → -ℤ' (-ℤ' x) ≡ x
-ℤ'-invol = /elimProp (λ _ → trunc _ _) λ _ → refl _

-------- transports -------
-- Cubical Agda has a primitive transp type. 

-- transport is the special case where interval variable is i0
transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p x = transp (λ i → p i) i0 x

-- transportRefl doesn't hold trivially
transportRefl : (x : A) → transport (refl A) x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

-- can be ued to _prove_ the J-rule
J : {x : A} (P : (y : A) → x ≡ y → Type ℓ) (d : P x (refl x))
    {y : A} (p : x ≡ y) → P y p
J P d p = transport (λ i → P (p i) λ j → p (i ∧ j)) d

-- The computation/β-rule holds up to a path!
J-β : {x : A} (P : (y : A) → x ≡ y → Type ℓ) (d : P x (refl x))
    → J P d (refl x) ≡ d -- P y p
J-β P d = transportRefl d


------ univalence ------
-- Let's define ≃:

fiber : (f : A → B) (b : B) → Type _
fiber {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)

isEquiv : (f : A → B) → Type _
isEquiv {B = B} f = (b : B) → isContr (fiber f b)

_≃_  : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B  = Σ[ f ∈ (A → B) ] (isEquiv f)

-- Digression --
-- _≃_ is _not_ the same as an isomorphism. They are
-- logically equvalent but not equivalent as types! We often, however,
-- exhibit terms of type A ≃ B by constructin an isomorphism between them
--

isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
isProp-isEquiv f = isOfHLevelΠ 1 λ b → isPropIsContr

-- consequence: equivalences are uniquely determined by their underlying functoins

≃-equality : {f g : A ≃ B} → fst f ≡ fst g → f ≡ g
fst (≃-equality p i) = p i
snd (≃-equality {f = f} {g = g} p i) = help i
  where
  help : PathP (λ i → isEquiv (p i)) (snd f) (snd g)
  help = isOfHLevelPathP 0 ((snd g) , λ y → isProp-isEquiv (fst g) (snd g) y)
           _ _ .fst

-- Note: obvious map 
ua⁻ : A ≡ B → A ≃ B
ua⁻ {A = A} = J (λ B p → A ≃ B) (idEquiv A)

-- univalence: ua⁻ is an equivalence
-- in particular: get
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i =
  Glue B (λ {(i = i0) → A , e ; (i = i1) → B , idEquiv B})

univalence' : Iso (A ≃ B) (A ≡ B)
Iso.fun univalence' = ua
Iso.inv univalence' = ua⁻
Iso.rightInv (univalence' {A = A} {B = B}) =
  J (λ B p → ua (ua⁻ p) ≡ p)
    (ap ua (J-β (λ B p → A ≃ B) (idEquiv A))
    ∙ uaIdEquiv)
  where
  uaIdEquiv : ua (idEquiv A) ≡ refl A
  uaIdEquiv i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , idEquiv A)
Iso.leftInv univalence' (f , iseq) =
  ≃-equality (funExt λ a
    → transportRefl (f (transport (refl _) a))
    ∙ ap f (transportRefl a))


univalence : (A ≃ B) ≃ (A ≡ B)
univalence = isoToEquiv univalence'


--- structures and univalence
record isSemiGroup (A : Type ℓ) (mult : A → A → A)  : Type ℓ where
  no-eta-equality
  field
    is-set : isSet A
    assoc : (x y z : A) → mult x (mult y z) ≡ mult (mult x y) z

open isSemiGroup

SemiGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
SemiGroup ℓ =
  Σ[ A ∈ Type ℓ ]
    Σ[ mult ∈ (A → A → A) ]
      isSemiGroup A mult

-- note: isSemiGroup is a _property_

isProp-isSemiGroup : {A : Type ℓ} {mult : A → A → A}
  → isProp (isSemiGroup A mult)
is-set (isProp-isSemiGroup {A = A} p q i) = isPropIsOfHLevel 2 (is-set p) (is-set q) i
assoc (isProp-isSemiGroup {A = A} p q i) x y z j = is-set p _ _ (assoc p x y z ) (assoc q x y z) i j

mult : ∀ {ℓ} (A : SemiGroup ℓ) → fst A → fst A → fst A
mult (A , (mult , p)) = mult


module _ {G H : SemiGroup ℓ} (ϕ : fst G ≃ fst H)
         (hom : (x y : _) → fst ϕ (mult G x y) ≡ mult H (fst ϕ x) (fst ϕ y)) where
  private
    multG = fst (snd G)
    multH = fst (snd H)

    type-path : fst G ≡ fst H
    type-path = ua ϕ

    mult-path : PathP (λ i → type-path i → type-path i → type-path i) multG multH
    mult-path = toPathP (funExt λ x → funExt λ y
      → transportRefl (fst ϕ (multG (invEq ϕ (transport (refl _) x)) (invEq ϕ (transport (refl _) y))))
       ∙ (ap (fst ϕ) (λ i → multG (invEq ϕ (transportRefl x i)) (invEq ϕ (transportRefl y i)))
       ∙ (hom (invEq ϕ x) (invEq ϕ y)
       ∙ λ i → multH (secEq ϕ x i) (secEq ϕ y i))))

    

  SIP-semiGroup :  G ≡ H
  fst (SIP-semiGroup i) = type-path i
  fst (snd (SIP-semiGroup i)) = mult-path i
  snd (snd (SIP-semiGroup i)) = goal i
    where
    goal : PathP (λ i → isSemiGroup (type-path i) (mult-path i)) (snd (snd G)) (snd (snd H))
    goal = toPathP (isProp-isSemiGroup _ _)

-- example
ℕ-Semi : SemiGroup ℓ-zero
fst ℕ-Semi = ℕ
fst (snd ℕ-Semi) = _+_
is-set (snd (snd ℕ-Semi)) = isSetℕ
assoc (snd (snd ℕ-Semi)) = +-assoc


data Bool : Type where
  𝟘 : Bool
  𝟙 : Bool 

data ListBin : Type where
  []    : ListBin
  _∷_   : (x : Bool) (xs : ListBin) → ListBin
  drop0 : 𝟘 ∷ [] ≡ []

