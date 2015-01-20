module ECC.Tests.Comp where
-- Untested.

open import ECC.Main hiding (Type) renaming (AnyType to Type)

import Level as Le
open import Data.Unit

infixl 8 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Le.Lift ⊤
A ^ suc n = A × A ^ n

^-foldr : ∀ {n α β} {A : Set α} {B : Set β}
        -> (A -> B -> B) -> B -> A ^ n -> B
^-foldr {0}     f z  []      = z
^-foldr {suc n} f z (x , xs) = f x (^-foldr f z xs)

levels : ℕ -> Set
levels n = level ^ n

Σ-ᵀVec : ∀ {n} -> levels n -> Set
Σ-ᵀVec {0}      _       = ⊤
Σ-ᵀVec {suc n} (α , αs) = Σ (Type α) λ X -> ᵀ⟦ X ⟧ -> Σ-ᵀVec αs

fold-Σ-Vec-ℓ : ∀ {n} -> levels n -> level -> level
fold-Σ-Vec-ℓ αs β = ^-foldr _⊔ᵢ_ β αs

fold-Σ-Vec : ∀ {n β} {αs : levels n} -> Σ-ᵀVec αs -> Type β -> Type (fold-Σ-Vec-ℓ αs β)
fold-Σ-Vec {0}      _      Y = Y
fold-Σ-Vec {suc n} (X , F) Y = X Π λ x -> fold-Σ-Vec (F x) Y

compᵀ : ∀ n {β γ} {αs : levels n} {Y : Type β} {Xs : Σ-ᵀVec αs}
      -> ᵀ⟦ fold-Σ-Vec Xs Y ⟧
      -> (ᵀ⟦ Y ⟧ -> Type γ)
      -> Type (fold-Σ-Vec-ℓ αs γ)
compᵀ  0                   y Z = Z y
compᵀ (suc n) {Xs = X , _} g Z = X Π λ x -> compᵀ n (g x) Z

-- For simplicity the result of (g) doesn't depend on anything.
comp : ∀ n {β γ} {αs : levels n} {Y : Type β} {Z : ᵀ⟦ Y ⟧ -> Type γ} {Xs : Σ-ᵀVec αs}
     -> Term (Y Π Z)
     -> (g : Term (fold-Σ-Vec Xs Y))
     -> Term (compᵀ n ⟦ g ⟧ Z)
comp  0      f y = f · y
comp (suc n) f g = ⇧ λ x -> comp n f (g · ↑ x)
