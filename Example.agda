{-# OPTIONS --without-K #-}
module Example
 (C0 : Set)
 (C1 : C0 → C0 → Set)
 (C2 : (a b c : C0) (ab : C1 a b) (ac : C1 a c) (bc : C1 b c) → Set)
 (C3 : (a b c d : C0) (ab : C1 a b) (ac : C1 a c) (bc : C1 b c) (ad : C1 a d) (bd : C1 b d) (cd : C1 c d)
       (abc : C2 a b c ab ac bc) (abd : C2 a b d ab ad bd) (acd : C2 a c d ac ad cd) (bcd : C2 b c d bc bd cd)
       → Set)
 where

open import SemiSimplicialType

data C : Set where
  c-1 : C
  c0 : C0 → C
  c1 : (a b : C0) (ab : C1 a b) → C
  c2 : (a b c : C0) (ab : C1 a b) (ac : C1 a c) (bc : C1 b c) (abc : C2 a b c ab ac bc) → C
  c3 : (a b c d : C0) (ab : C1 a b) (ac : C1 a c) (bc : C1 b c) (ad : C1 a d) (bd : C1 b d) (cd : C1 c d)
       (abc : C2 a b c ab ac bc) (abd : C2 a b d ab ad bd) (acd : C2 a c d ac ad cd) (bcd : C2 b c d bc bd cd)
       (abcd : C3 a b c d ab ac bc ad bd cd abc abd acd bcd) → C

∂ : (c : C) → Cube C
∂ c-1 = leaf c-1
∂ (c0 x) = node (leaf ⟨ c-1 , (c0 x) ⟩)
∂ (c1 a b ab) = node (node (leaf ⟨ ⟨ c-1 , c0 a ⟩ , ⟨ c0 b , c1 a b ab ⟩ ⟩))
∂ (c2 a b c ab ac bc abc) = node (node (node (leaf ⟨ ⟨ ⟨ c-1 ,  c0 a ⟩ ,      ⟨ c0 b ,      c1 a b ab ⟩ ⟩ ,
                                                     ⟨ ⟨ c0 c , c1 a c ac ⟩ , ⟨ c1 b c bc , c2 a b c ab ac bc abc ⟩ ⟩ ⟩)))
∂ (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) =
  node (node (node (node (leaf ⟨
     ⟨ ⟨ ⟨ c-1 , c0 a ⟩ , ⟨ c0 b , c1 a b ab  ⟩ ⟩ ,
       ⟨ ⟨ c0 c , c1 a c ac ⟩ , ⟨ c1 b c bc , c2 a b c ab ac bc abc ⟩ ⟩ ⟩ ,
     ⟨ ⟨ ⟨ c0 d , c1 a d ad ⟩ , ⟨ c1 b d bd , c2 a b d ab ad bd abd ⟩ ⟩ ,
       ⟨ ⟨ c1 c d cd , c2 a c d ac ad cd acd ⟩ , ⟨ c2 b c d bc bd cd bcd , c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd ⟩ ⟩ ⟩ ⟩))))

apex-axiom : (c : C) → apex (∂ c) ≡ c
apex-axiom c-1 = refl
apex-axiom (c0 _) = refl
apex-axiom (c1 _ _ _) = refl
apex-axiom (c2 _ _ _ _ _ _ _) = refl
apex-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl

nadir-axiom : (c : C) → nadir (∂ c) ≡ c-1
nadir-axiom c-1 = refl
nadir-axiom (c0 _) = refl
nadir-axiom (c1 _ _ _) = refl
nadir-axiom (c2 _ _ _ _ _ _ _) = refl
nadir-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = refl

reduce-axiom : (c : C) {χ : Cube C} → χ ≤ ∂ c → ∂ (apex χ) ≡ χ
reduce-axiom c-1 ε = refl
reduce-axiom (c0 _) (N ε) = refl
reduce-axiom (c0 _) (Y ε) = refl
reduce-axiom (c1 _ _ _) (N N ε) = refl
reduce-axiom (c1 _ _ _) (N Y ε) = refl
reduce-axiom (c1 _ _ _) (Y N ε) = refl
reduce-axiom (c1 _ _ _) (Y Y ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (N N N ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (N N Y ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (N Y N ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (N Y Y ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (Y N N ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (Y N Y ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (Y Y N ε) = refl
reduce-axiom (c2 _ _ _ _ _ _ _) (Y Y Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N N N N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N N N Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N N Y N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N N Y Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N Y N N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N Y N Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N Y Y N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (N Y Y Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y N N N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y N N Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y N Y N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y N Y Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y Y N N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y Y N Y ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y Y Y N ε) = refl
reduce-axiom (c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (Y Y Y Y ε) = refl

Example : Sst
Example = sst C c-1 ∂ apex-axiom nadir-axiom reduce-axiom
