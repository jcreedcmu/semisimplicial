{-# OPTIONS --without-K #-}
module Util where
open import Level

data ℕ : Set where
 z : ℕ
 s : ℕ → ℕ

data ⊤ : Set where
 unit : ⊤

record Sq (A : Set) : Set where constructor ⟨_,_⟩ ; field fst snd : A
open Sq public

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where refl : {a : A} → a ≡ a
infixr 5 _≡_

inv : ∀ {ℓ} {A : Set ℓ} → {x y : A} → x ≡ y → y ≡ x
inv refl = refl

_•_ : ∀ {ℓ} {A : Set ℓ} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl • refl = refl
infixr 10 _•_

ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

coe : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} → x ≡ y → P x → P y
coe refl x = x

-- stuff about propositions

is-prop : ∀ {ℓ} → Set ℓ → Set ℓ
is-prop A = (a b : A) → a ≡ b

left-inverse : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → refl ≡ inv p • p
left-inverse refl = refl

prop-unique-path : ∀ {ℓ} → {A : Set ℓ} (f : is-prop A) (x y z : A) (p : y ≡ z) → p ≡ inv (f x y) • (f x z)
prop-unique-path f x y .y refl = left-inverse (f x y)

prop-is-set : ∀ {ℓ} {A : Set ℓ} (f : is-prop A) → (a b : A) (p q : a ≡ b) → p ≡ q
prop-is-set f a b p q = prop-unique-path f a a b p • inv (prop-unique-path f a a b q)

-- Haven't yet used these?

apd : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (f : (x : A) → P x) →
    (p : x ≡ y) → coe p (f x) ≡ f y
apd f refl = refl

coe-to-• : {A : Set} {x y z : A} → (p : y ≡ z) (q : x ≡ y) → coe p q ≡ q • p
coe-to-• refl refl = refl

refl-left-id : {A : Set} {y z : A} → (p : y ≡ z) → p ≡ refl • p
refl-left-id refl = refl

l2r-post : {A : Set} {x y z : A} → (p : y ≡ z) (q : x ≡ y) (r : x ≡ z) → q • p ≡ r → p ≡ (inv q) • r
l2r-post refl refl r h = h • refl-left-id r

coeap : {A B : Set} {P : B → Set} {f : A → B} (x y : A) (p : x ≡ y) (e : (P (f x))) →
       coe {P = P} (ap f p) e ≡ coe {P = λ x → P (f x)} p e
coeap x .x refl e = refl

coe2 : {A : Set} {P : A → Set} (a1 a2 b : A) (p1 : a1 ≡ b) (p2 : a2 ≡ b) (x1 : P a1) (x2 : P a2)
   → coe {P = P} p1 x1 ≡ coe {P = P} p2 x2
coe2 a1 .a1 .a1 refl refl x1 x2 = {!!}

-- module Foo where

--   P-prop : ∀ {ℓ ℓ'} (Cb : Set ℓ) (P : Cb → Set ℓ') → Set (ℓ ⊔ ℓ')
--   P-prop Cb P = (x y : Cb) → P x → P y → x ≡ y

--   P-prop-unique-path : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f : P-prop A P) (x y z : A) (p : y ≡ z)
--            → (px : P x) (py : P y) (pz : P z)
--            → p ≡ inv (f x y px py) • (f x z px pz)
--   P-prop-unique-path f x y .y refl px py pz = {!left-inverse (f x y !}

--   lemma : (Cb : Set) (P : Cb → Set)
--           (x y : Cb) → P x → P y → (p q : x ≡ y) → p ≡ q
--   lemma = {!!}
