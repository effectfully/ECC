module ECC.Tests.Props where
-- Taken from https://www.labri.fr/perso/casteran/CoqArt/depprod/impred.html

open import ECC.Main

ᵀ⊥ : Propᵀ
ᵀ⊥ = prop Π id

ᵀ¬ : Propᵀ -> Propᵀ
ᵀ¬ P = P ⟶ ᵀ⊥

ᵀ∃ : ∀ {α} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Propᵀ) -> Propᵀ
ᵀ∃ A P = prop Π λ R -> (A Π λ x -> P x ⟶ R) ⟶ R

_∧_ : Propᵀ -> Propᵀ -> Propᵀ
P ∧ Q = prop Π λ R -> (P ⟶ Q ⟶ R) ⟶ R

fst-∧ : Term (prop Π λ P -> prop Π λ Q -> P ∧ Q ⟶ P)
fst-∧ = ⇧ λ P -> ⇧ λ Q -> ⇧ λ F -> ↑ F · ↑ P · plain const

ᵀex = ᵀℕ
    Π λ α -> type α -- Note the (Π) instead of the (ℓΠ). 
    Π λ A -> (A ⟶ prop)
    Π λ P -> A
    Π λ x -> P x ⟶ ᵀ∃ A P

ex : Term ᵀex
ex = ⇧ λ α -> ⇧ λ A -> ⇧ λ P -> ⇧ λ x -> ⇧ λ p -> ⇧ λ R -> ⇧ λ f -> ↑ f · ↑ x · ↑ p

ᵀ¬-∃ : Propᵀ
ᵀ¬-∃ = ᵀℕ
     Π λ α -> type α
     Π λ A -> (A ⟶ prop)
     Π λ P -> ᵀ¬ (ᵀ∃ A P)
     ⟶ A
     Π λ x -> ᵀ¬ (P x)

¬-∃ : Term ᵀ¬-∃
¬-∃ = ⇧ λ α -> ⇧ λ A -> ⇧ λ P -> ⇧ λ f -> ⇧ λ x -> ⇧ λ p ->
  ↑ f · (ex · ↑ _ · ↑ _ · ↑ _ · ↑ x · ↑ p)
