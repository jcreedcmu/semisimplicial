{-# OPTIONS --without-K #-}
module Theory where

open import SemiSimplicialType

nadir-lemma : {C : Set} → (χ : Cube C) → leaf (nadir χ) ≤ χ
nadir-lemma (leaf x) = ε
nadir-lemma (node χ) = N (nadir-lemma χ)

module _ (X : Sst) where
 open Sst X

 -- returns the number of axes along which the cube varies.
 data cubeIsDim : {C : Set} → (χ : Cube C) (n : ℕ) → Set1 where
   cube/leaf : (c : C) → cubeIsDim (leaf c) z
   cube/suc : {C : Set} (χ : Cube (Sq C)) (n : ℕ) → cubeIsDim χ n → cubeIsDim (node χ) (s n)

 -- actually returns the dimension of the boundary cube, which is one
 -- greater than the notional dimension of the cell itself.
 data isDim (c : C) (n : ℕ) : Set1 where
   dim/ : cubeIsDim (∂ c) n → isDim c n

 ⋆-boundary-lemma : ∂ ⋆ ≡ leaf ⋆
 ⋆-boundary-lemma = ap ∂ (inv (nadir-axiom ⋆ ))
                     • reduce-axiom ⋆ (nadir-lemma (∂ ⋆))
                     • ap leaf (nadir-axiom ⋆)

 any-cubedim-minus-1-has-cell : (χ : Cube C) → cubeIsDim χ z → C
 any-cubedim-minus-1-has-cell (leaf c) cid = c

 any-cubedim-minus-1-is-leaf : (χ : Cube C) (p : cubeIsDim χ z) → χ ≡ leaf (any-cubedim-minus-1-has-cell χ p)
 any-cubedim-minus-1-is-leaf (leaf c) cid = refl

 any-boundary-leaf-is-leaf-⋆ : {c d : C} → ∂ c ≡ leaf d → ⋆ ≡ d
 any-boundary-leaf-is-leaf-⋆ {c} p = inv (nadir-axiom c) • ap nadir p

 any-dim-minus-1-has-leaf-⋆ : (c : C) (p : isDim c z) → ∂ c ≡ leaf ⋆
 any-dim-minus-1-has-leaf-⋆ c (dim/ p) = path • ap leaf (inv (any-boundary-leaf-is-leaf-⋆ path)) where
         path : ∂ c ≡ leaf (any-cubedim-minus-1-has-cell (∂ c) p)
         path = any-cubedim-minus-1-is-leaf (∂ c) p

 -- ⋆ is the unique cell with dimension -1

 ⋆-has-dim-minus-1 : isDim ⋆ z
 ⋆-has-dim-minus-1 = dim/ (coe  {P = λ hole → cubeIsDim hole z} (inv ⋆-boundary-lemma) (cube/leaf ⋆))

 any-dim-minus-1-is-⋆ : (c : C) (p : isDim c z) → c ≡ ⋆
 any-dim-minus-1-is-⋆ c p = inv (apex-axiom c) • ap apex (any-dim-minus-1-has-leaf-⋆ c p)
