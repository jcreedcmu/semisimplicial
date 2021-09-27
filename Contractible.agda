{-# OPTIONS --without-K #-}
module Contractible where

open import SemiSimplicialType renaming (z to zero)

module _ (X : Sst) where
 open Sst X

 -- record cube-for (c : C) : Set1 where
 --   constructor mkcf
 --   field
 --     d : C
 --     χ : Cube C
 --     im : χ ≡ ∂ d
 --     a : apex χ ≡ c

 -- is-prop (  χ is in image of ∂ and apex χ = c

 -- cube-for-is-prop : (c : C) → is-prop (cube-for c)
 -- cube-for-is-prop c (mkcf d .(∂ d) refl a) (mkcf d' .(∂ d') refl a') = {!!}

 -- lemma2 : (c : C) → (p q : (mkcf (apex (∂ c)) (∂ (apex (∂ c))) refl (apex-axiom _ • apex-axiom _)) ≡
 --                            (mkcf c (∂ c) refl (apex-axiom _))) → p ≡ q
 -- lemma2 c p q = prop-is-set (cube-for-is-prop c)
 --         (mkcf (apex (∂ c)) (∂ (apex (∂ c))) refl (apex-axiom _ • apex-axiom _))
 --         (mkcf c (∂ c) refl (apex-axiom _)) p q

 valid-to-apex : (χ : Cube C) → valid ∂ χ → ∂ (apex χ) ≡ χ
 valid-to-apex .(∂ c) (v/ c) = ap ∂ (apex-axiom c)

 -- valid-wit : {χ : Cube C} → valid ∂ χ → C
 -- valid-wit (v/ c) = c

 -- valid-axiom : {χ : Cube C} (v : valid ∂ χ) → ∂ (valid-wit v) ≡ χ
 -- valid-axiom (v/ c) = refl

 -- valid-wit-is-apex : (χ : Cube C) (v : valid ∂ χ) → apex χ ≡ valid-wit v
 -- valid-wit-is-apex .(∂ c) (v/ c) = apex-axiom c


 -- valid-is : (χ : Cube C) (v : valid ∂ χ) → v ≡ coe {P = valid ∂} (valid-axiom v) (v/ {∂ = ∂} (valid-wit v))
 -- valid-is .(∂ c) (v/ c) = refl

 -- valid-is2 : (χ : Cube C) (v : valid ∂ χ) → v ≡ coe {P = valid ∂} (valid-to-apex χ v) (v/ {∂ = ∂} (apex χ))
 -- valid-is2 .(∂ c) (v/ c) = {!!}

 valid-is-prop : (χ : Cube C) → is-prop (valid ∂ χ)
 valid-is-prop = {!!}

 reduce-axiom' : (c : C) {χ : Cube C} → χ ≤ ∂ c → ∂ (apex χ) ≡ χ
 reduce-axiom' c {χ} p = valid-to-apex χ (reduce-axiom c p)

 reduce-apex-coherence : (c d : C) (ℓ : ∂ d ≤ ∂ c) → reduce-axiom' c ℓ ≡ ap ∂ (apex-axiom d)
 reduce-apex-coherence c d ℓ =
    ap (valid-to-apex (∂ d)) (valid-is-prop (∂ d) (reduce-axiom c ℓ) (v/ d))

 -- Goal: valid-to-apex (∂ d) (reduce-axiom c ℓ) ≡ ap ∂ (apex-axiom d)
 -- suppose reduce-axiom c ℓ --> v/ c'
 -- then: valid-to-apex (∂ d) (reduce-axiom c ℓ) --> ap ∂ (apex-axiom c')

 -- lemma d (reduce-axiom' c ℓ) (ap ∂ (apex-axiom d)) where
 --   lemma : (c : C) → (p q : ∂ (apex (∂ c)) ≡ ∂ c) → p ≡ q
 --   lemma = {!!}
