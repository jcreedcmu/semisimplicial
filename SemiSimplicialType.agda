{-# OPTIONS --without-K #-}
module SemiSimplicialType where

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where refl : {a : A} → a ≡ a

record Sq (A : Set) : Set where constructor ⟨_,_⟩ ; field fst snd : A
open Sq

data Cube : (C : Set) → Set1 where
 leaf : {C : Set} → C → Cube C
 node : {C : Set} → Cube (Sq C) → Cube C

cmap : {C D : Set} → (f : C → D) → Cube C → Cube D
cmap f (leaf x) = leaf (f x)
cmap f (node c) = node (cmap (λ (⟨ x , y ⟩) → ⟨ f x , f y ⟩) c)

data _≤_ : {C : Set} → Cube C → Cube C → Set1 where
  ε : {C : Set} {c : C} → leaf c ≤ leaf c
  Y_ : {C : Set} {χ χ' : Cube (Sq C)} → χ ≤ χ' → node χ ≤ node χ'
  N_ : {C : Set} {χ χ' : Cube (Sq C)} → χ ≤ χ' → cmap fst χ ≤ node χ'

pole : {C : Set} → ({C : Set} → Sq C → C) → Cube C → C
pole f (leaf c) = c
pole f (node s) = f (pole f s)

nadir = λ {C : Set} → pole {C} fst
apex = λ {C : Set} → pole {C} snd

record SemiSimplicialType : Set1 where
  constructor sst
  field
    C : Set
    ⋆ : C
    ∂ : (c : C) → Cube C
    apex-axiom : (c : C) → apex (∂ c) ≡ c
    nadir-axiom : (c : C) → nadir (∂ c) ≡ ⋆
    reduce-axiom : (c : C) {χ : Cube C} → χ ≤ ∂ c → ∂ (apex χ) ≡ χ
