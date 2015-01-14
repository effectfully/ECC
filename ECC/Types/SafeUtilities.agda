module ECC.Types.SafeUtilities where

open import ECC.Types.Basic
open import ECC.Types.Utilities hiding (≤⌈_⌉) public

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

generalizeᴸ-left : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> level
generalizeᴸ-left = uncurryᵂ go where
  go : ∀ {α' α} {A' : Type α'} {A : Type α} -> (le : A' ≤ A) -> ≤⟦ le ⟧ -> level
  go     {A = _  Π _    } le _ = ω
  go     {A = _ ℓΠ _    } le _ = ω
  go     {A = _ ≥Π _    } le _ = ω
  go     {A = ᵀΣ {α} A B} le p = α ⊔ go (le Σ· proj₁ p) (proj₂ p)
  go     {A = Lift A    } le x = go (unL≤L le) x
  go {α'}                 le x = α'

generalizeᴸ-right : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
                  -> ≤⟦ le ⟧ᵂ -> ℕ -> ℕ -> level
generalizeᴸ-right x ′α ′′α = uncurryᵂ go x where
  go : ∀ {α' α} {A' : Type α'} {A : Type α}
     -> (le : A' ≤ A) -> ≤⟦ le ⟧ -> level
  go        {A = type α    } le   _ with α | α ≟ ′α
  ... | ._ | yes refl = ᴺ (suc ′′α)
  ... | α' | no  _    = ᴺ (suc α')
  go        {A = A  Π B    } le   _ = ω
  go        {A = A ℓΠ B    } le   _ = ω
  go        {A = A ≥Π B    } le   _ = ω
  go        {A = ᵀΣ {α} A B} le p = α ⊔ go (le Σ· proj₁ p) (proj₂ p)
  go        {A = Lift A    } le x = go (unL≤L le) x
  go {α = α}                 le _ = α

generalizeᵀ-left : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
                 -> (x : ≤⟦ le ⟧ᵂ) -> Type (generalizeᴸ-left x)
generalizeᵀ-left = uncurryᵂ go where
  go : ∀ {α' α} {A' : Type α'} {A : Type α}
     -> (le : A' ≤ A) -> (x : ≤⟦ le ⟧) -> Type (generalizeᴸ-left (tagWith le x))
  go {A' = A'} {prop  } le _ = A'
  go {A' = A'} {unit  } le _ = A'
  go {A' = A'} {ᵀℕ    } le _ = A'
  go {A' = A'} {type α} le _ = A'
  go       {A = A  Π B} le f = A ℓΠ λ x -> go (le  Π·     x) (f      x)
  go       {A = A ℓΠ B} le f = A ℓΠ λ x -> go (le ℓΠ·     x) (f      x)
  go       {A = A ≥Π B} le f = A ℓΠ λ x -> go (le ≥Π· tag x) (f (tag x))
  go       {A = ᵀΣ A B} le p = ᵀΣ A λ _ -> go (le Σ· proj₁ p) (proj₂ p)
  go       {A = Lift A} le x = go (unL≤L le) x

generalizeᵀ-right : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
                  -> (x : ≤⟦ le ⟧ᵂ) -> ∀ ′α ′′α -> Type (generalizeᴸ-right x ′α ′′α)
generalizeᵀ-right x ′α ′′α = uncurryᵂ go x where
  go : ∀ {α' α} {A' : Type α'} {A : Type α}
     -> (le : A' ≤ A) -> (x : ≤⟦ le ⟧) -> Type (generalizeᴸ-right (tagWith le x) ′α ′′α)
  go {A = prop  } le _ = prop
  go {A = unit  } le _ = unit
  go {A = ᵀℕ    } le _ = ᵀℕ
  go {A = type α} le _ with α | α ≟ ′α
  ... | ._ | yes refl = type ′′α
  ... | α' | no  _    = type α'
  go {A = A  Π B} le f = A ℓΠ λ x -> go (le  Π·     x) (f      x)
  go {A = A ℓΠ B} le f = A ℓΠ λ x -> go (le ℓΠ·     x) (f      x)
  go {A = A ≥Π B} le f = A ℓΠ λ x -> go (le ≥Π· tag x) (f (tag x))
  go {A = ᵀΣ A B} le p = ᵀΣ A λ _ -> go (le Σ· proj₁ p) (proj₂ p)
  go {A = Lift A} le x = go (unL≤L le) x

generalize : ∀ {α' α ′α ′′α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
           -> (x : ≤⟦ le ⟧ᵂ)
           -> (′α≤′′α : ′α ≤ℕᵂ ′′α)
           -> generalizeᵀ-left x ≤ generalizeᵀ-right x ′α ′′α
generalize {′α = ′α} {′′α} x ′α≤′′α = uncurryᵂ go x where
  go : ∀ {α' α} {A' : Type α'} {A : Type α}
     -> (le : A' ≤ A)
     -> (x : ≤⟦ le ⟧)
     -> generalizeᵀ-left (tagWith le x) ≤ generalizeᵀ-right (tagWith le x) ′α ′′α
  go {A = prop  } le _ = le
  go {A = unit  } le _ = le
  go {A = ᵀℕ    } le _ = le
  go {A = type α} le _ with α | α ≟ ′α
  ... | ._ | yes refl = ≤-type-trans le (el ′α≤′′α)
  ... | _  | no  _    = le
  go {A = A  Π B} le f = ℓΠ≤ℓΠ λ x -> go (le  Π·     x) (f      x)
  go {A = A ℓΠ B} le f = ℓΠ≤ℓΠ λ x -> go (le ℓΠ·     x) (f      x)
  go {A = A ≥Π B} le f = ℓΠ≤ℓΠ λ x -> go (le ≥Π· tag x) (f (tag x))
  go {A = ᵀΣ A B} le p =  Σ≤Σ  λ _ -> go (le Σ· proj₁ p) (proj₂ p)
  go {A = Lift A} le x = go (unL≤L le) x

last-level : ∀ {α} -> Type α -> ℕ
last-level (type α) = α
last-level (A  Π B) = last-level (B      (inhabit A))
last-level (A ℓΠ B) = last-level (B      (inhabit A))
last-level (A ≥Π B) = last-level (B (tag (inhabit A)))
last-level (ᵀΣ A B) = last-level (B      (inhabit A))
last-level (Lift A) = last-level A
last-level  _       = 0

-- This function retags a value like the one from the Utilities module,
-- however it doesn't allow you to change the meaning of the value.
-- All (Π≤Π) tags become (ℓΠ≤ℓΠ), which is annoying, but I have no idea, how to fix this.
≤⌈_⌉ : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
     -> (x : ≤⟦ le ⟧ᵂ) {′α : ℕ} {≤′α : last-level A ≤ℕᵂ ′α}
     -> ≤⟦ generalize x ≤′α ⟧ᵂ
≤⌈_⌉ x {≤′α = ≤′α} = tagWith (generalize x ≤′α) (uncurryᵂ go x ≤′α) where
  go : ∀ {α' α} {A' : Type α'} {A : Type α}
     -> (le : A' ≤ A)
     -> (x : ≤⟦ le ⟧) {′α ′′α : ℕ} 
     -> (′α≤′′α : ′α ≤ℕᵂ ′′α)
     -> ≤⟦ generalize (tagWith le x) ′α≤′′α ⟧
  go {A = prop  } le A      ′α≤′′α = A
  go {A = unit  } le _      ′α≤′′α = _
  go {A = ᵀℕ    } le n      ′α≤′′α = n
  go {A = type α} le A {′α} ′α≤′′α with α | α ≟ ′α
  ... | ._ | yes refl = A
  ... | _  | no  _    = A
  go {A = A  Π B} le f      ′α≤′′α = λ x -> go (le  Π·     x) (f      x)  ′α≤′′α
  go {A = A ℓΠ B} le f      ′α≤′′α = λ x -> go (le ℓΠ·     x) (f      x)  ′α≤′′α
  go {A = A ≥Π B} le f      ′α≤′′α = λ x -> go (le ≥Π· tag x) (f (tag x)) ′α≤′′α
  go {A = ᵀΣ A B} le p      ′α≤′′α = proj₁ p , go (le Σ· proj₁ p) (proj₂ p) ′α≤′′α
  go {A = Lift A} le x             = go (unL≤L le) x

ᵀ⌈_⌉ : ∀ {α'} {A' : Type α'}
     -> (x : ᵀ⟦ A' ⟧ᵂ) {′α : ℕ} {≤′α : last-level A' ≤ℕᵂ ′α} 
     -> ≤⟦ generalize (ᵀ-to-≤ x) ≤′α ⟧ᵂ
ᵀ⌈ x ⌉ {≤′α = ≤′α} = ≤⌈ ᵀ-to-≤ x ⌉ {≤′α = ≤′α}

private
  example : ≤⌈ tagWith ( Π≤Π  {A = type 0} λ _ -> ᵀ≤ᵀ {α = 3}) id ⌉
          ≡    tagWith (ℓΠ≤ℓΠ {A = type 0} λ _ -> ᵀ≤ᵀ {α = 5}) id
  example = refl
