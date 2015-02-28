module ECC.Tests.Comp where
-- Untested.

open import ECC.Main
  renaming (Type to Typeᴺ; Universe to Type)

import Level as Le
open import Data.Unit

infixl 8 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = Le.Lift ⊤
A ^ suc n = A × A ^ n

^-foldr : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B -> B) -> B -> A ^ n -> B
^-foldr {0}     f z  []      = z
^-foldr {suc n} f z (x , xs) = f x (^-foldr f z xs)

levels : ℕ -> Set
levels n = level ^ n

Types : ∀ {n} -> levels n -> Set
Types {0}      _       = ⊤
Types {suc n} (α , αs) = Σ (Type α) λ X -> ᵀ⟦ X ⟧ -> Types αs

_⊔ⁿ_ : ∀ {n} -> levels n -> level -> level
_⊔ⁿ_ αs β = ^-foldr _⊔ᵢ_ β αs

_->ⁿ_ : ∀ {n β} {αs : levels n} -> Types αs -> Type β -> Type (αs ⊔ⁿ β)
_->ⁿ_ {0}      _      Y = Y
_->ⁿ_ {suc n} (X , F) Y = X Π λ x -> F x ->ⁿ Y

Comp : ∀ n {β γ} {αs : levels n} {Y : Type β} {Xs : Types αs}
     -> (ᵀ⟦ Y ⟧ -> Type γ) -> ᵀ⟦ Xs ->ⁿ Y ⟧ -> Type (αs ⊔ⁿ γ)
Comp  0                   Z y = Z y
Comp (suc n) {Xs = X , _} Z g = X Π λ x -> Comp n Z (g x)

-- For simplicity the result of (g) doesn't depend on anything.
comp : ∀ n {β γ} {αs : levels n} {Y : Type β} {Z : ᵀ⟦ Y ⟧ -> Type γ} {Xs : Types αs}
     -> Term (Y Π Z) -> (g : Term (Xs ->ⁿ Y)) -> Term (Comp n Z ⟦ g ⟧)
comp  0      f y = f · y
comp (suc n) f g = ⇧ λ x -> comp n f (g · ↑ x)



I : Term (type 1 Π λ A -> A ⟶ A)
I = ⇧ λ A -> ⇧ λ x -> ↑ x

g : Term (type 0 Π λ A -> A ⟶ type 0)
g = ⇧ λ A -> ⇧ λ x -> ↓ ᵀℕ

-- (αs) supposed to be inferred automatically. Why not, Agda?
test : Term (type 0 Π λ A -> A ⟶ type 0)
test = comp 2 {αs = _ , _ , _} (I · ↑ _) g
