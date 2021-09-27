{-# OPTIONS --without-K #-}
module SemiSimplicialType where
open import Util public

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
pole f (node sq) = f (pole f sq)

nadir = λ {C : Set} → pole {C} fst
apex = λ {C : Set} → pole {C} snd

-- Semi-simplicial types
record Sst : Set1 where
  constructor sst
  field
    C : Set
    ⋆ : C
    ∂ : (c : C) → Cube C
    apex-axiom : (c : C) → apex (∂ c) ≡ c
    nadir-axiom : (c : C) → nadir (∂ c) ≡ ⋆
    reduce-axiom : (c : C) {χ : Cube C} → χ ≤ ∂ c → ∂ (apex χ) ≡ χ

data valid {C : Set} (∂ : (c : C) → Cube C) : (χ : Cube C) → Set1 where
  v/ : (c : C) → valid ∂ (∂ c)

record Sst' : Set1 where
  constructor sst'
  field
    C : Set
    ⋆ : C
    ∂ : (c : C) → Cube C
    apex-axiom : (c : C) → apex (∂ c) ≡ c
    nadir-axiom : (c : C) → nadir (∂ c) ≡ ⋆
    int : (c : C) {χ : Cube C} → χ ≤ ∂ c → valid ∂ χ
