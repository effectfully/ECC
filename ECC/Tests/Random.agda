module ECC.Tests.Random where

open import ECC.Main

ᵀtest-1 : Type 2
ᵀtest-1 = (type 1 ≥⟶ type 1)
          ≥Π λ B -> type 0 
           Π λ A -> el B ᵀ⌈ A ⌉

ᵀtest-2 : Type 2
ᵀtest-2 = (type 1 ≥Π λ A -> el A ⟶ type 1)
          Π λ B -> type 0 
          Π λ A -> B ⌈ typeᴮ 0 ⌉ A

ᵀtest-3 : Type 2
ᵀtest-3 = (type 1 ≥Π el)
          ≥Π λ B -> (type 0 ⟶ el B ⌈ typeᴮ 0 ⌉)
           Π λ f -> type 0
           Π λ x -> el B ⌈ typeᴮ 0 ⌉

test-3 : Term ᵀtest-3
test-3 = ≥⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x

ᵀtest-4 : Type 2
ᵀtest-4 = (type 1 ≥Π el)
          ≥Π λ B -> (type 0 ⟶ el B ⌈ typeᴮ 0 ⌉)
          ≥Π λ f -> type 0
          ≥Π λ x -> el B ⌈ typeᴮ 0 ⌉

ᵀtest-5 : Type 2
ᵀtest-5 = (type 1 ≥Π λ A -> el A)
          ≥Π λ B -> el B ⌈ typeᴮ 0 ⌉

ᵀtest-6 : Type 3
ᵀtest-6 = (type 2 Π λ A -> A ⟶ type 1)
          ≥Π λ B -> el B (type 1) (type 0)

ᵀtest-7 : Type 2
ᵀtest-7 = (ᵀℕ ⟶ type 1)
          ≥Π λ B -> (ᵀℕ Π el B)
           Π λ f -> el B 0

test-7 : Term ᵀtest-7
test-7 = ≥⇧ λ B -> ⇧ λ f -> ↑ f · plain 0

ᵀtest-8 : Propᵀ
ᵀtest-8 = (type 0 Π id) ≥Π λ B -> el B prop ⟶ el B prop

test-8 : Term ᵀtest-8
test-8 = ≥⇧ λ B -> ⇧ λ x -> ↑ x

test-9 : Term _
test-9 = test-8 ≥· tagWith (≤-refl (type 0 Π id)) inhabit

test-10 : Term _
test-10 = test-8 ≥· tagWith (Π≤Π ≤-refl) inhabit

ᵀtest-11 : Type 2
ᵀtest-11 = (type 1 ≥⟶ type 1)
           Π λ p -> type 1
          ≥Π λ c -> p c

ᵀtest-12 : Type 2
ᵀtest-12 = (type 1 ≥⟶ type 1)
           Π λ p -> type 0
          ≥Π λ c -> p ≤⌈ c ⌉
-- ≤⌈_⌉ is too restricted and complicated. Would it be better to replace it with (≤-trans)?
