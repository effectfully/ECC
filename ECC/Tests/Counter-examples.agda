module ECC.Tests.Counter-examples where

open import ECC.Main

-- This typechecks, but (el ≤⌈ f ⌉ ≢ el f).
-- Precisely (el ≤⌈ f ⌉ ≡ λ _ -> el f 0)
ᵀcounter-1 : Typeᴺ 2
ᵀcounter-1 = ((ᵀℕ ⟶ ᵀℕ) ≥⟶ type 1)
           Π λ p -> (ᵀℕ ⟶ ᵀℕ)
          ≥Π λ f -> p ≤⌈ f ⌉
