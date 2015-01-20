module ECC.Types.Level where

open import ECC.Utilities

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (module _≤_; _≤_) renaming (_⊔_ to _⊔ℕ_) public
open import Data.Product

infix 4 _≤ℕ_ _≤ℕᵂ_
infixl 6 _⊔ℕᵢ_ _⊔̂ℕᵢ_ _⊔ᵢ_ _⊔_

-- If (n ∸ m) is in canonical form,
-- then (n ≤ℕ m) reduces either to (⊤) or to (⊥).
-- The value of (⊤) can be inferred automatically,
-- which is exploited by the (ᵀ≤ᵀ) constructor of the (_≤_) datatype.
-- It would be nice to have a type error, when (n ≤ℕ m) reduces to (⊥).
_≤ℕ_ : ℕ -> ℕ -> Set
0     ≤ℕ _     = ⊤
suc _ ≤ℕ 0     = ⊥
suc n ≤ℕ suc m = n ≤ℕ m 

≤ℕ-refl : ∀ n -> n ≤ℕ n
≤ℕ-refl  0      = _
≤ℕ-refl (suc n) = ≤ℕ-refl n

≤ℕ-trans : ∀ n {m p} -> n ≤ℕ m -> m ≤ℕ p -> n ≤ℕ p
≤ℕ-trans  zero   {m    } {p    } n≤m m≤p = _
≤ℕ-trans (suc _) {zero } {p    } ()  m≤p
≤ℕ-trans (suc n) {suc m} {zero } n≤m ()
≤ℕ-trans (suc n) {suc m} {suc p} n≤m m≤p = ≤ℕ-trans n n≤m m≤p 

⊔ℕ-≤ℕ : ∀ n {m p} -> n ≤ℕ p -> m ≤ℕ p -> n ⊔ℕ m ≤ℕ p
⊔ℕ-≤ℕ  0      {m    } {p    } n≤m m≤p = m≤p
⊔ℕ-≤ℕ (suc _) {0    } {p    } n≤m m≤p = n≤m
⊔ℕ-≤ℕ (suc n) {suc m} {0    } n≤m ()
⊔ℕ-≤ℕ (suc n) {suc m} {suc p} n≤m m≤p = ⊔ℕ-≤ℕ n n≤m m≤p

_⊔ℕᵢ_ : ℕ -> ℕ -> ℕ
n ⊔ℕᵢ 0 = 0
n ⊔ℕᵢ m = n ⊔ℕ m

⊔ℕᵢ-≤ℕ : ∀ n {m p} -> n ≤ℕ p -> m ≤ℕ p -> n ⊔ℕᵢ m ≤ℕ p
⊔ℕᵢ-≤ℕ n {0}     {p} n≤m m≤p = _
⊔ℕᵢ-≤ℕ n {suc m} {p} n≤m m≤p = ⊔ℕ-≤ℕ n n≤m m≤p

_≤ℕᵂ_ : ℕ -> ℕ -> Set
n ≤ℕᵂ m = Tag (uncurry _≤ℕ_) (n , m)

_⊔̂ℕᵢ_ : ∀ {n m p} -> n ≤ℕᵂ p -> m ≤ℕᵂ p -> n ⊔ℕᵢ m ≤ℕᵂ p
_⊔̂ℕᵢ_ {n} {m} (tag n≤p) (tag m≤p) = tag (⊔ℕᵢ-≤ℕ n {m} n≤p m≤p)

data level : Set where
  # : ℕ -> level
  ω : level

pred# : level -> ℕ
pred# (# n) = pred n
pred#  ω    = 0

_⊔ᵢ_ : level -> level -> level
# n ⊔ᵢ # m = # (n ⊔ℕᵢ m)
# 0 ⊔ᵢ β   = β
_   ⊔ᵢ _   = ω

_⊔_ : level -> level -> level
# n ⊔ # m = # (n ⊔ℕ m)
_   ⊔ _   = ω

_≤ℓ_ : level -> level -> Set
# α ≤ℓ # β = α ≤ℕ β
_   ≤ℓ ω   = ⊤
ω   ≤ℓ _   = ⊥
