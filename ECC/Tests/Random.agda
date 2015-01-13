module ECC.Tests.Random where

open import ECC.Main

ᵀtest-1 : Typeᴺ 2
ᵀtest-1 = (type 1 ≥⟶ type 1)
          ≥Π λ B -> type 0 
          ᵂΠ λ A -> el B ⌈ A ⌉

ᵀtest-2 : Typeᴺ 2
ᵀtest-2 = (type 1 ≥Π λ A -> el A ⟶ type 1)
          Π λ B -> type 0 
          Π λ A -> B ⌈ typeᵂ 0 ⌉ A

ᵀtest-3 : Typeᴺ 2
ᵀtest-3 = (type 1 ≥Π el)
          ≥Π λ B -> (type 0 ⟶ el B ⌈ typeᵂ 0 ⌉)
           Π λ f -> type 0
           Π λ x -> el B ⌈ typeᵂ 0 ⌉

test-3 : Term ᵀtest-3
test-3 = ≥⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x

ᵀtest-4 : Typeᴺ 2
ᵀtest-4 = (type 1 ≥Π el)
          ≥Π λ B -> (type 0 ⟶ el B ⌈ typeᵂ 0 ⌉)
          ≥Π λ f -> type 0
          ≥Π λ x -> el B ⌈ typeᵂ 0 ⌉

ᵀtest-5 : Typeᴺ 2
ᵀtest-5 = (type 1 ≥Π λ A -> el A)
          ≥Π λ B -> el B ⌈ typeᵂ 0 ⌉

ᵀtest-6 : Typeᴺ 3
ᵀtest-6 = (type 2 Π λ A -> A ⟶ type 1)
          ≥Π λ B -> el B (type 1) (type 0)

ᵀtest-7 : Typeᴺ 2
ᵀtest-7 = ((type 1 ⟶ type 1) ≥⟶ type 1)
          Π λ B -> (type 1 ⟶ type 0)
         ᵂΠ λ C -> B ⌈ C ⌉

ᵀtest-8 : Typeᴺ 2
ᵀtest-8 = ((type 1 ≥⟶ type 1) ≥⟶ type 1)
          Π λ B -> (type 1 ≥⟶ type 0)
         ᵂΠ λ C -> B ⌈ C ⌉

-- _π_ : ∀ {α β}
--     -> (A : Type α) {B : ᵀ⟦ A ⟧ -> Type β}
--     -> ((x : ᵀ⟦ A ⟧) -> ᵀ⟦ B x ⟧ᵂ)
--     -> ᵀ⟦ A Π B ⟧ᵂ

ᵀtest-9 : Typeᴺ 2
ᵀtest-9 = (ᵀℕ ⟶ type 1)
          ≥Π λ B -> (ᵀℕ Π el B)
           Π λ f -> el B 0

test-9 : Term ᵀtest-9
test-9 = ≥⇧ λ B -> ⇧ λ f -> ↑ f · plain 0

ᵀtest-10 : ᵀProp
ᵀtest-10 = (type 0 Π id) ≥Π λ B -> el B prop ⟶ el B prop

test-10 : Term ᵀtest-10
test-10 = ≥⇧ λ B -> ⇧ λ x -> ↑ x

test-11 : Term _
test-11 = test-10 ≥· tagWith (≤-refl (type 0 Π id)) inhabit

test-12 : Term _
test-12 = test-10 ≥· tagWith (Π≤Π ≤-refl) inhabit

ᵀtest-13 : Typeᴺ 2
ᵀtest-13 = (type 1 ≥⟶ type 1)
           Π λ p -> type 1
          ≥Π λ c -> p c

ᵀtest-14 : Typeᴺ 2
ᵀtest-14 = (type 1 ≥⟶ type 1)
           Π λ p -> type 0
          ≥Π λ c -> p ≤⌈ c ⌉
