{-# OPTIONS --without-K #-}
module Preimage where
open import Util
open import Level

module Foo {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  L = ℓ ⊔ ℓ'

  record fiber {f : A → B} (b : B) : Set L where
    field
     a : A
     p : f a ≡ b

  -- mono : (f : A → B) →
  -- fiber-set : {f : A →
  data preimage  (f : A → B) : (b : B) → Set L where
    pre/ : (a : A) → preimage f (f a)

  data injective (f : A → B) : Set L where
    inj/ : (g : B → A) → ((a : A) → g (f a) ≡ a) → injective f

  -- lemmax : {a1 a2 : A} (f : A → B) → (inj : injective f) → (p : f a1 ≡ f a2) → ap f (inj p) ≡ p
  -- lemmax = {!!}

  lemma2 : {a1 a2 : A} (f : A → B) → injective f → (p : f a1 ≡ f a2) → ≡over {B = preimage f} (pre/ a1) (pre/ a2) p
  lemma2 f (inj/ g x) p = {!!}

  lemma : {b1 b2 : B} (f : A → B) → injective f →
          (v1 : preimage f b1) (v2 : preimage f b2) (p : b1 ≡ b2) → ≡over {B = preimage f} v1 v2 p
  lemma f ij (pre/ a1) (pre/ a2) p = lemma2 f ij p

  lemma3 : {b : B} (f : A → B) → injective f → (v1 v2 : preimage f b) → v1 ≡ v2
  lemma3 {b} f ij v1 v2 = lemma {b1 = b} {b2 = b} f ij v1 v2 refl
