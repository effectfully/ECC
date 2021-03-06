module ECC.Tests.FromExplicitSubtyping where
-- Tests are from the "A calculus of constructions with explicit subtyping" paper.

open import ECC.Main

ᵀtest-1 : Type 2
ᵀtest-1 = type 0
          Π λ a -> type 0
          Π λ b -> (a ⟶ b)
          Π λ f -> (type 1 ≥Π λ c -> el c)
          Π λ g -> b

test-1 : Term ᵀtest-1
test-1 = ⇧ λ a -> ⇧ λ b -> ⇧ λ f -> ⇧ λ g -> ↑ f · (↑ g ≥· ᵀ⌈ el a ⌉)
 
ᵀtest-1' : Type 2
ᵀtest-1' = type 0
           Π λ a -> type 0
           Π λ b -> (a ⟶ b)
           Π λ f -> (type 1 Π λ c -> c)
           Π λ g -> b
         
test-1' : Term ᵀtest-1'
test-1' = ⇧ λ a -> ⇧ λ b -> ⇧ λ f -> ⇧ λ g -> ↑ f · lower (↑ g · ↑ a ⟰ ᵀ≤ᵀ)

ᵀtest-2 : Type 2
ᵀtest-2 = (type 1 ≥⟶ type 1)
          Π λ p -> (type 1 ≥⟶ type 1)
          Π λ q -> (type 0 Π λ c -> p ᵀ⌈ c ⌉ ⟶ q ᵀ⌈ c ⌉)
          Π λ f -> (type 1 ≥Π λ a -> type 1 ≥Π λ b -> p (a ⟶̃ b))
          Π λ g -> type 0
          Π λ a -> type 0
          Π λ b -> q ᵀ⌈ a ⟶ b ⌉

test-2 : Term ᵀtest-2
test-2 = ⇧ λ p -> ⇧ λ q -> ⇧ λ f -> ⇧ λ g -> ⇧ λ a -> ⇧ λ b ->
   ↑ f · ↓ (el a ⟶ el b) · (↑ g ≥· ᵀ⌈ el a ⌉ ≥· ᵀ⌈ el b ⌉)

ᵀtest-2' : Type 2
ᵀtest-2' = (type 1 ⟶ type 1)
           Π λ p -> (type 1 ⟶ type 1)
           Π λ q -> (type 0 Π λ c -> p (Lift c) ⟶ q (Lift c))
           Π λ f -> (type 1 Π λ a -> type 1 Π λ b -> p (a ⟶ b))
           Π λ g -> type 0
           Π λ a -> type 0
           Π λ b -> q (Lift (a ⟶ b))

-- The problem, described in the paper:
-- test-2' : Term ᵀtest-2'
-- test-2' = ⇧ λ p -> ⇧ λ q -> ⇧ λ f -> ⇧ λ g -> ⇧ λ a -> ⇧ λ b -> {!!}
  -- ↑ f · ↓ (el a ⟶ el b)
  --   : Term (el p (Lift (el a ⟶ el b)) ⟶ el q (Lift (el a ⟶ el b)))
  -- ↑ g · (↑ a ⟰ ᵀ≤ᵀ) · (↑ b ⟰ ᵀ≤ᵀ)
  --   : Term (el p (Lift (el a) ⟶ Lift (el b)))
