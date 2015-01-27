module ECC.Terms.LeBasic where

open import ECC.Types.Basic

infixl 4 _·_ _ℓ·_ _≥·_

mutual
  record T̃erm {α' α} (A' : Type α') (A : Type α) : Set where
    inductive
    constructor _∈̃_
    field
      term : Term A'
      le : A' ≤ A

  data Term : ∀ {α} -> Type α -> Set where
    -- Handles variables, types at the value level and plain Agda values.
    -- We can't use simple (ᵀ⟦ A ⟧) here, because Agda can't infer (A) from (ᵀ⟦ A ⟧).
    ↑ : ∀ {α} {A : Type α} -> ᵀ⟦ A ⟧ᵂ -> Term A
    -- Lambda abstractions.
    ⇧ : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
      -> ((x : ᵀ⟦ A ⟧ᵂ) -> Term (B (el x)))
      -> Term (A Π B)
    ℓ⇧ : ∀ {α} {A : Type α} {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
       -> ((x : ᵀ⟦ A ⟧ᵂ) -> Term (B (el x)))
       -> Term (A ℓΠ B)
    ≥⇧ : ∀ {α} {A : Type α} {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
           {B : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le)}
       -> (∀ {α'} {A' : Type α'} {le : A' ≤ A} -> (x : ≤⟦ le ⟧ᵂ) -> Term (B x))
       -> Term (A ≥Π B)
    -- Applications.
    _·_ : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
        -> Term (A Π B) -> (x : Term A) -> Term (B ⟦ x ⟧)
    _ℓ·_ : ∀ {α} {A : Type α} {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
         -> Term (A ℓΠ B) -> (x : Term A) -> Term (B ⟦ x ⟧)
    _≥·_ : ∀ {α' α} {A' : Type α'} {A : Type α}
             {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
             {B : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le)}
         -> Term (A ≥Π B) -> (x : T̃erm A' A) -> Term (B _)
    -- Pairs.
    pair : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
         -> (x : Term A) -> Term (B ⟦ x ⟧) -> Term (ᵀΣ A B)
    fst : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
        -> Term (ᵀΣ A B) -> Term A
    snd : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
        -> (p : Term (ᵀΣ A B)) -> Term (B (proj₁ ⟦ p ⟧))
    -- Lifting stuff.
    lift  : ∀ {α' α} {α'≤α : α' ≤ℓ α} {A' : Type α'}
          -> Term A' -> Term (Lift {α = α} {α'≤α} A')
    lower : ∀ {α' α} {α'≤α : α' ≤ℓ α} {A' : Type α'}
          -> Term (Lift {α = α} {α'≤α} A') -> Term A'
    -- Kind of a subsumption rule.
    coerce : ∀ {α' α} {A' : Type α'} {A : Type α} -> T̃erm A' A -> Term A

  ⟦_⟧ : ∀ {α} {A : Type α} -> Term A -> ᵀ⟦ A ⟧
  ⟦ ↑ x             ⟧ = el x
  ⟦  ⇧ f            ⟧ = λ x -> ⟦ f (tag x) ⟧
  ⟦ ℓ⇧ f            ⟧ = λ x -> ⟦ f (tag x) ⟧
  ⟦ ≥⇧ f            ⟧ = λ x -> ⟦ f      x  ⟧
  ⟦ f  · x          ⟧ = ⟦ f ⟧ ⟦ x ⟧
  ⟦ f ℓ· x          ⟧ = ⟦ f ⟧ ⟦ x ⟧
  ⟦ f ≥· (x ∈̃ le)   ⟧ = ⟦ f ⟧ (ᵀtag ⟦ x ⟧ ⇅ le)
  ⟦ pair x y        ⟧ = ⟦ x ⟧ , ⟦ y ⟧
  ⟦ fst p           ⟧ = proj₁ ⟦ p ⟧
  ⟦ snd p           ⟧ = proj₂ ⟦ p ⟧
  ⟦ lift  x         ⟧ = ⟦ x ⟧
  ⟦ lower x         ⟧ = ⟦ x ⟧
  ⟦ coerce (x ∈̃ le) ⟧ = ⟦ x ⟧ ᵀ⟰ le

-- Types at the value level.
↓ : ∀ {α} -> Type (# α) -> Term (type α)
↓ = ↑ ∘ tag

-- Plain Agda values. Good for types too.
plain : ∀ {α} {A : Type α} -> ᵀ⟦ A ⟧ -> Term A
plain = ↑ ∘ tag
