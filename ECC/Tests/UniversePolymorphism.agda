module ECC.Tests.UniversePolymorphism where

open import ECC.Main

open import Function
open import Relation.Binary.PropositionalEquality

z : Term ((ᵀℕ ⟶ ᵀℕ) ℓΠ λ k -> type (suc (k 0)))
z = ℓ⇧ λ k -> ↓ (type (el k 0))

s : Term (((ᵀℕ ⟶ ᵀℕ) ⟶ ᵀℕ)
         ℓΠ λ j -> ((ᵀℕ ⟶ ᵀℕ) ℓΠ λ k -> type (suc (j k)))
         ⟶ (ᵀℕ ⟶ ᵀℕ)
         ℓΠ λ k -> type (suc (k zero ⊔ℕ j (k ∘ suc))))
s = ℓ⇧ λ j -> ⇧ λ r -> ℓ⇧ λ k ->
  ↓ (type (el k 0) ⟶ ⟦ ↑ r ℓ· ⇧ (λ α -> ↑ k · (plain suc · ↑ α)) ⟧)

crescendo : Term (((ᵀℕ ⟶ ᵀℕ) ⟶ ᵀℕ)
                 ℓΠ λ j -> ((ᵀℕ ⟶ ᵀℕ) ℓΠ λ k -> type (j k))
                 ⟶ type (j id))
crescendo = ℓ⇧ λ j -> ⇧ λ r -> ↑ r ℓ· plain id

test : ⟦ crescendo ℓ· ↑ _ · (s ℓ· ↑ _ · (s ℓ· ↑ _ · (s ℓ· ↑ _ · z))) ⟧
     ≡ (type 0 ⟶ type 1 ⟶ type 2 ⟶ type 3)
test = refl

-- A direct equivalent of

-- z : (k : Level -> Level) -> Set (suc (k zero))
-- z k = Set (k zero)

-- s : {j : (Level -> Level) -> Level}
--   -> ((k : Level -> Level) -> Set (suc (j k)))
--   -> (k : Level -> Level)
--   -> Set (suc (k zero ⊔ j (k ∘ suc)))
-- s r k = Set (k zero) -> r (k ∘ suc)
  
-- crescendo : {j : (Level -> Level) -> Level}
--           -> ((k : Level -> Level) -> Set (j k)) -> Set (j id)
-- crescendo r = r id

-- test : crescendo (s (s (s z))) ≡ (Set₀ -> Set₁ -> Set₂ -> Set₃)
-- test = refl
