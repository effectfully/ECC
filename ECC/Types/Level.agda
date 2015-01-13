module ECC.Types.Level where

open import ECC.Utilities

open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (module _≤_; _≤_) renaming (_⊔_ to _⊔ℕ_) public
open import Data.Product

infix 4 _≤ℕ_ _≤ℓᵂ_

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

⊔-≤ℕ : ∀ n {m p} -> n ≤ℕ p -> m ≤ℕ p -> n ⊔ℕ m ≤ℕ p
⊔-≤ℕ  0      {m    } {p    } n≤m m≤p = m≤p
⊔-≤ℕ (suc _) {0    } {p    } n≤m m≤p = n≤m
⊔-≤ℕ (suc n) {suc m} {0    } n≤m ()
⊔-≤ℕ (suc n) {suc m} {suc p} n≤m m≤p = ⊔-≤ℕ n n≤m m≤p

data level : Set where
  -1 : level
  ᴺ  : ℕ -> level
  ω  : level

predᴺ : level -> level
predᴺ (ᴺ  0)      = -1
predᴺ (ᴺ (suc α)) = ᴺ α
predᴺ α = α -- This case doesn't appear in the code.

_⊔ᵢ_ : level -> level -> level
α   ⊔ᵢ -1  = -1
-1  ⊔ᵢ β   = β
ᴺ α ⊔ᵢ ᴺ β = ᴺ (α ⊔ℕ β)
_   ⊔ᵢ _   = ω

_⊔_ : level -> level -> level
α   ⊔ -1  = α
-1  ⊔ β   = β
ᴺ α ⊔ ᴺ β = ᴺ (α ⊔ℕ β)
_   ⊔ _   = ω

_≤ℓ_ : level -> level -> Set
-1  ≤ℓ _   = ⊤
ᴺ α ≤ℓ ᴺ β = α ≤ℕ β
_   ≤ℓ ω   = ⊤
_   ≤ℓ _   = ⊥

_≤ℕᵂ_ : ℕ -> ℕ -> Set
n ≤ℕᵂ m = Tag (uncurry _≤ℕ_) (n , m)

_≤ℓᵂ_ : level -> level -> Set
α ≤ℓᵂ β = Tag (uncurry _≤ℓ_) (α , β)
