module ECC.Types.Utilities where

open import ECC.Types.Basic

infixl 0 _∋_

_∋_ : ∀ {α} -> (A : Type α) -> ᵀ⟦ A ⟧ -> ᵀ⟦ A ⟧ᵂ
_∋_ = tagWith {B = ᵀ⟦_⟧}

propᵂ = type 0 ∋ prop
unitᵂ = prop   ∋ unit
ᵀℕᵂ   = type 0 ∋ ᵀℕ

typeᵂ : ∀ α -> _
typeᵂ α = type (suc α) ∋ type α

_➘_  : ∀ {α β} {B : Type β} -> (A : Type α) -> ᵀ⟦ B ⟧ᵂ -> ᵀ⟦ A  ⟶ B ⟧ᵂ
A  ➘ tag y = A  ⟶ _ ∋ λ _ -> y

_≥➘_ : ∀ {α β} {B : Type β} -> (A : Type α) -> ᵀ⟦ B ⟧ᵂ -> ᵀ⟦ A ≥⟶ B ⟧ᵂ
A ≥➘ tag y = A ≥⟶ _ ∋ λ _ -> y

inhabit-type : ∀ α -> Type α
inhabit-type (ᴺ 0)       = prop
inhabit-type (ᴺ (suc α)) = type α
inhabit-type  -1         = unit
inhabit-type  ω          = ᵀℕ ℓΠ type

inhabit : ∀ {α} -> (A : Type α) -> ᵀ⟦ A ⟧
inhabit  prop          = unit
inhabit  unit          = _
inhabit  ᵀℕ            = 0
inhabit (type  0     ) = prop
inhabit (type (suc α)) = type α
inhabit (A  Π B)       = λ x -> inhabit (B x)
inhabit (A ℓΠ B)       = λ x -> inhabit (B x)
inhabit (A ≥Π B)       = λ x -> inhabit (B x)
inhabit (ᵀΣ A B)       = let IA = inhabit A in IA , inhabit (B IA)
inhabit (Lift A)       = inhabit A

≤-type-trans : ∀ {α' α ′α} {A' : Type α'}
             -> A' ≤ type α -> α ≤ℕ ′α -> A' ≤ type ′α
≤-type-trans {′α = ′α}    (p≤ᵀ {α})           α≤′α = p≤ᵀ {′α}
≤-type-trans {ᴺ (suc α')} (ᵀ≤ᵀ {α'≤α = α'≤α}) α≤′α = ᵀ≤ᵀ {α'≤α = ≤ℕ-trans α' α'≤α α≤′α}

⌈_/_⌉ᵀ : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A}
       -> (∀ {α' α} {A' : Type α'} {A : Type α} -> A' ≤ A -> Set) -> ≤⟦ le ⟧ᵂ -> Set
⌈_/_⌉ᵀ {A = prop  }      Cont _ = Cont p≤p
⌈_/_⌉ᵀ {A = unit  }      Cont _ = Cont ⊤≤⊤
⌈_/_⌉ᵀ {A = ᵀℕ    }      Cont _ = Cont ℕ≤ℕ
-- There are two cases: (prop ≤ type α) and (type α' ≤ type α).
⌈_/_⌉ᵀ {A = type α} {le} Cont _ = ∀ {′α} {α≤′α : α ≤ℕ ′α} -> Cont (≤-type-trans le α≤′α)
⌈_/_⌉ᵀ {A = A  Π B} {le} Cont f = let IA =      inhabit A  in
  ⌈ (λ le' -> Cont ( Π≤Π  {A = A} λ _ -> le')) / tagWith (le  Π· IA) (el f IA) ⌉ᵀ
⌈_/_⌉ᵀ {A = A ℓΠ B} {le} Cont f = let IA =      inhabit A  in
  ⌈ (λ le' -> Cont (ℓΠ≤ℓΠ {A = A} λ _ -> le')) / tagWith (le ℓΠ· IA) (el f IA) ⌉ᵀ
⌈_/_⌉ᵀ {A = A ≥Π B} {le} Cont f = let IA = tag (inhabit A) in
  ⌈ (λ le' -> Cont (≥Π≥Π  {A = A} λ _ -> le')) / tagWith (le ≥Π· IA) (el f IA) ⌉ᵀ
⌈_/_⌉ᵀ {A = ᵀΣ A B} {le} Cont p =
  ⌈ (λ le' -> Cont ( Σ≤Σ  {A = A} λ _ -> le')) / tagWith (le  Σ· _) (proj₂ (el p)) ⌉ᵀ
⌈_/_⌉ᵀ {A = Lift A} {le} Cont x = ⌈ Cont / tagWith (unL≤L le) (el x) ⌉ᵀ
 
-- What about this?
-- ⌈ (λ {α'} {α} le -> ∀ {′α} {α'≤′α : α' ≤ℓ ′α} {α≤′α : α ≤ℓ ′α} ->
--      Cont (L≤L {α'≤′α = α'≤′α} {α≤′α} le)) / tagWith (unL≤L le) (el x) ⌉ᵀ

-- When (x) is a tagged value or a tagged function, that ignores ALL its arguments,
-- we can retag it. I.e. if (le : A' ≤ A) and (x : ≤⟦ le ⟧ᵂ),
-- then forall (′A), such that (A ≤ ′A), this function constructs such (le'), that
-- (le' : A' ≤ ′A), (≤⌈ x ⌉ : ≤⟦ le' ⟧ᵂ) and el x ≡ el ≤⌈ x ⌉.
-- (Check this for the (ᵀΣ) and (Lift) cases.)
≤⌈_⌉ : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A} -> (x : ≤⟦ le ⟧ᵂ) -> ⌈ ≤⟦_⟧ᵂ / x ⌉ᵀ
≤⌈_⌉ {A = A} (tag x) = go tag A x where
  go : ∀ {α' α} {A' : Type α'}
         {Cont : ∀ {α' α} {A' : Type α'} {A : Type α} -> A' ≤ A -> Set}
     -> (cont : ∀ {α' α} {A' : Type α'} {A : Type α} {le : A' ≤ A} -> ≤⟦ le ⟧ -> Cont le)
     -> (A : Type α) {le : A' ≤ A}
     -> (x : ≤⟦ le ⟧) 
     -> ⌈ Cont / tagWith le x ⌉ᵀ
  go cont  prop    A = cont A
  go cont  unit    _ = cont _
  go cont  ᵀℕ      n = cont n
  go cont (type α) A = cont A
  go cont (A  Π B) f = go (λ x -> cont λ             _ -> x)  (B _) _
  go cont (A ℓΠ B) f = go (λ x -> cont λ             _ -> x)  (B _) _
  go cont (A ≥Π B) f = go (λ x -> cont λ {_} {_} {_} _ -> x)  (B _) _
  go cont (ᵀΣ A B) p = go (λ x -> cont (proj₁ p         , x)) (B _) _
  go cont (Lift A) x = go cont A x

-- This retagging is annoying. Is it avoidable?
⌈_⌉ : ∀ {α'} {A' : Type α'} -> (x : ᵀ⟦ A' ⟧ᵂ) -> ⌈ ≤⟦_⟧ᵂ / tagWith (≤-refl A') (el x) ⌉ᵀ
⌈_⌉ {A' = A'} x = ≤⌈ tagWith (≤-refl A') (el x) ⌉

private
  open import Relation.Binary.PropositionalEquality

  example : ≤⌈ tagWith (Π≤Π {A = ᵀℕ} λ _ -> ᵀ≤ᵀ {α = 3}) (λ _ -> type 0) ⌉
          ≡    tagWith (Π≤Π {A = ᵀℕ} λ _ -> ᵀ≤ᵀ {α = 5}) (λ _ -> type 0)
  example = refl
