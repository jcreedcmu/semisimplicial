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

int : (c : C) {χ : Cube C} → χ ≤ ∂ c → valid ∂ χ
int c-1 ε = v/ c-1
int (c0 a) (N ε) = v/ c-1
int (c0 a) (Y ε) = v/ (c0 a)
int (c1 a b ab) (N N ε) = v/ c-1
int (c1 a b ab) (N Y ε) = v/ (c0 b)
int (c1 a b ab) (Y N ε) = v/ (c0 a)
int (c1 a b ab) (Y Y ε) = v/ (c1 a b ab)
int (c2 a b c ab ac bc abc) (N N N ε) = v/ c-1
int (c2 a b c ab ac bc abc) (N N Y ε) = v/ (c0 c)
int (c2 a b c ab ac bc abc) (N Y N ε) = v/ (c0 b)
int (c2 a b c ab ac bc abc) (N Y Y ε) = v/ (c1 b c bc)
int (c2 a b c ab ac bc abc) (Y N N ε) = v/ (c0 a)
int (c2 a b c ab ac bc abc) (Y N Y ε) = v/ (c1 a c ac)
int (c2 a b c ab ac bc abc) (Y Y N ε) = v/ (c1 a b ab)
int (c2 a b c ab ac bc abc) (Y Y Y ε) = v/ (c2 a b c ab ac bc abc)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N N N N ε) = v/ c-1
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N N N Y ε) = v/ (c0 d)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N N Y N ε) = v/ (c0 c)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N N Y Y ε) = v/ (c1 c d cd)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N Y N N ε) = v/ (c0 b)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N Y N Y ε) = v/ (c1 b d bd)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N Y Y N ε) = v/ (c1 b c bc)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (N Y Y Y ε) = v/ (c2 b c d bc bd cd bcd)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y N N N ε) = v/ (c0 a)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y N N Y ε) = v/ (c1 a d ad)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y N Y N ε) = v/ (c1 a c ac)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y N Y Y ε) = v/ (c2 a c d ac ad cd acd)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y Y N N ε) = v/ (c1 a b ab)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y Y N Y ε) = v/ (c2 a b d ab ad bd abd)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y Y Y N ε) = v/ (c2 a b c ab ac bc abc)
int (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd) (Y Y Y Y ε) = v/ (c3 a b c d ab ac bc ad bd cd abc abd acd bcd abcd)

Example : Sst'
Example = sst' C c-1 ∂ apex-axiom nadir-axiom int
