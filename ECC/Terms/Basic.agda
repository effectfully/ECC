module ECC.Terms.Basic where

open import ECC.Types.Basic public

infixl 4 _·_ _ℓ·_ _≥·_

mutual
  data Term : ∀ {α} -> Type α -> Set where
    tt : Term unit
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
    _≥·_ : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
             {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
             {B : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le)}
         -> Term (A ≥Π B) -> (x : ≤⟦ le ⟧ᵂ) -> Term (B x)
      -- We could also have (≤Term le) with an appropriate (≤⟦_⟧)
      -- instead of just (≤⟦ le ⟧ᵂ), but this approach is too restricted
      -- and doesn't look very useful.
    pair : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
         -> (x : Term A) -> Term (B ⟦ x ⟧) -> Term (ᵀΣ A B)
    fst : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
        -> Term (ᵀΣ A B) -> Term A
    snd : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
        -> (p : Term (ᵀΣ A B)) -> Term (B (proj₁ ⟦ p ⟧))
    lift  : ∀ {α' α} {α'≤α : α' ≤ℓ α} {A' : Type α'}
          -> Term A' -> Term (Lift {α = α} {α'≤α} A')
    lower : ∀ {α' α} {α'≤α : α' ≤ℓ α} {A' : Type α'}
          -> Term (Lift {α = α} {α'≤α} A') -> Term A'
    -- Kind of a subsumption rule.
    _⟰_ : ∀ {α' α} {A' : Type α'} {A : Type α} -> Term A' -> A' ≤ A -> Term A

  ⟦_⟧ : ∀ {α} {A : Type α} -> Term A -> ᵀ⟦ A ⟧
  ⟦ tt       ⟧ = _
  ⟦ ↑ x      ⟧ = el x
  ⟦  ⇧ f     ⟧ = λ x -> ⟦ f (tag x) ⟧
  ⟦ ℓ⇧ f     ⟧ = λ x -> ⟦ f (tag x) ⟧
  ⟦ ≥⇧ f     ⟧ = λ x -> ⟦ f      x  ⟧
  ⟦ f  · x   ⟧ = ⟦ f ⟧ ⟦ x ⟧
  ⟦ f ℓ· x   ⟧ = ⟦ f ⟧ ⟦ x ⟧
  ⟦ f ≥· x   ⟧ = ⟦ f ⟧   x
  ⟦ pair x y ⟧ = ⟦ x ⟧ , ⟦ y ⟧
  ⟦ fst p    ⟧ = proj₁ ⟦ p ⟧
  ⟦ snd p    ⟧ = proj₂ ⟦ p ⟧
  ⟦ lift  x  ⟧ = ⟦ x ⟧
  ⟦ lower x  ⟧ = ⟦ x ⟧
  ⟦ x ⟰ le  ⟧ = ᵀcoerce ⟦ x ⟧ le

-- Types at the value level.
-- Doesn't handle props (like (unit)). Is there a simple way to fix this?
↓ : ∀ {α} -> Typeᴺ α -> Term (type α)
↓ = ↑ ∘ tag

-- Plain Agda values. Good for types too.
plain : ∀ {α} {A : Type α} -> ᵀ⟦ A ⟧ -> Term A
plain = ↑ ∘ tag
