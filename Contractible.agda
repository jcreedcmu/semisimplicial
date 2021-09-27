{-# OPTIONS --without-K #-}
module Contractible where

open import SemiSimplicialType renaming (z to zero)

module _ (X : Sst) where
 open Sst X

 record cube-for (c : C) : Set1 where
   constructor mkcf
   field
     d : C
     χ : Cube C
     im : χ ≡ ∂ d
     a : apex χ ≡ c

 -- is-prop (  χ is in image of ∂ and apex χ = c

 cube-for-is-prop : (c : C) → is-prop (cube-for c)
 cube-for-is-prop c (mkcf d .(∂ d) refl a) (mkcf d' .(∂ d') refl a') = {!!}

 lemma2 : (c : C) → (p q : (mkcf (apex (∂ c)) (∂ (apex (∂ c))) refl (apex-axiom _ • apex-axiom _)) ≡
                            (mkcf c (∂ c) refl (apex-axiom _))) → p ≡ q
 lemma2 c p q = prop-is-set (cube-for-is-prop c)
         (mkcf (apex (∂ c)) (∂ (apex (∂ c))) refl (apex-axiom _ • apex-axiom _))
         (mkcf c (∂ c) refl (apex-axiom _)) p q

 reduce-apex-coherence : (c d : C) (ℓ : ∂ d ≤ ∂ c) → reduce-axiom c ℓ ≡ ap ∂ (apex-axiom d)
 reduce-apex-coherence c d ℓ = lemma d (reduce-axiom c ℓ) (ap ∂ (apex-axiom d)) where
   lemma : (c : C) → (p q : ∂ (apex (∂ c)) ≡ ∂ c) → p ≡ q
   lemma = {!!}
