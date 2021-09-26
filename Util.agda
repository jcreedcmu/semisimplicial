{-# OPTIONS --without-K #-}
module Util where

record Sq (A : Set) : Set where constructor ⟨_,_⟩ ; field fst snd : A
open Sq public

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where refl : {a : A} → a ≡ a

inv : ∀ {ℓ} {A : Set ℓ} → {x y : A} → x ≡ y → y ≡ x
inv refl = refl

_•_ : ∀ {ℓ} {A : Set ℓ} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl • refl = refl
infixr 10 _•_

ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

coe : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} → x ≡ y → P x → P y
coe refl x = x

data ℕ : Set where
 z : ℕ
 s : ℕ → ℕ
