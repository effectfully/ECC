{-# OPTIONS --no-positivity-check #-}

module ECC.Types.Basic where

open import ECC.Utilities   public
open import ECC.Types.Level public

open import Data.Unit using (⊤)
open import Data.Product    public

infixr 2 _Π_ _≥Π_ _⟶_ _≥⟶_
infix  1 _≤_

data Type : level -> Set
data _≤_ : ∀ {α' α} -> Type α' -> Type α -> Set
≤-refl : ∀ {α} -> (A : Type α) -> A ≤ A
≤⟦_⟧ : ∀ {α' α} {A' : Type α'} {A : Type α} -> A' ≤ A -> Set

Type# : ℕ -> Set
Type# = Type ∘ # 

-- (Prop) is reserved.
Propᵀ : Set
Propᵀ = Type# 0

-- An analog of (λ α -> Set α).
Typeᴺ : ℕ -> Set
Typeᴺ = Type# ∘ suc

-- An analog of (Setω).
Typeω : Set
Typeω = Type ω

ᵀ⟦_⟧ : ∀ {α} -> Type α -> Set
ᵀ⟦ A ⟧ = ≤⟦ ≤-refl A ⟧

-- (ᵀ⟦_⟧ᵂ = ≤⟦_⟧ᵂ ∘ ≤-refl)?
ᵀ⟦_⟧ᵂ : ∀ {α} -> Type α -> Set
ᵀ⟦_⟧ᵂ = Tag ᵀ⟦_⟧

≤⟦_⟧ᵂ : ∀ {α' α} {A' : Type α'} {A : Type α} -> A' ≤ A -> Set
≤⟦_⟧ᵂ = Tag ≤⟦_⟧

data Type where
  unit : Propᵀ
  ᵀℕ : Typeᴺ 0
  -- A predicative hierarchy of universes.
  type : ∀ α -> Type# (suc α)
  -- Induction-recursion as usual.
  _Π_ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Type β) -> Type (α ⊔ᵢ β)
  -- Just like in Agda, e.g. ((∀ α -> Set α) : Setω).
  _ℓΠ_ : ∀ {α} (A : Type α) {k : ᵀ⟦ A ⟧ -> level} -> (∀ x -> Type (k x)) -> Typeω
  -- A bounded dependent quantifier.
  _≥Π_ : ∀ {α}
       -> (A : Type α) {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
       -> (∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le))
       -> Type (α ⊔ᵢ k (≤-refl A)) -- Could (k (≤-refl A) ≤ℕ k A'≤A)?
  -- Do we need (_ℓ≥Π_)?
  ᵀΣ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Type β) -> Type (α ⊔ β)
  Lift : ∀ {α' α} {α'≤α : α' ≤ℓ α} -> Type α' -> Type α

prop : Typeᴺ 0
prop = type 0

typeᴺ : ∀ α -> Typeᴺ (suc α)
typeᴺ = type ∘ suc 

_⟶_  : ∀ {α β} -> Type α -> Type β -> Type (α ⊔ᵢ β)
A  ⟶ B = A  Π λ _ -> B

_≥⟶_ : ∀ {α β} -> Type α -> Type β -> Type (α ⊔ᵢ β)
A ≥⟶ B = A ≥Π λ _ -> B

_ᵂΠ_ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ᵂ -> Type β) -> Type (α ⊔ᵢ β)
A ᵂΠ B = A Π B ∘ tag

-- Πs are covariant only
data _≤_ where
  ⊤≤⊤ : unit ≤ unit
  ℕ≤ℕ : ᵀℕ ≤ ᵀℕ
  ᵀ≤ᵀ : ∀ {α' α} {α'≤α : α' ≤ℕ α} -> type α' ≤ type α
  Π≤Π : ∀ {α β' β} {A : Type α}
          {B' : ᵀ⟦ A ⟧ -> Type β'}
          {B  : ᵀ⟦ A ⟧ -> Type β }
      -> (∀ x -> B' x ≤ B x)
      -> A Π B' ≤ A Π B
  ℓΠ≤ℓΠ : ∀ {α} {A : Type α} {k' k : ᵀ⟦ A ⟧ -> level}
            {B' : ∀ x -> Type (k' x)}
            {B  : ∀ x -> Type (k  x)}
        -> (∀ x -> B' x ≤ B x)
        -> A ℓΠ B' ≤ A ℓΠ B
  ≥Π≥Π : ∀ {α} {A : Type α} {k' k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
           {B' : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k' le)}
           {B  : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k  le)}
       -> (∀ {α'} {A' : Type α'} {le : A' ≤ A} -> (x : ≤⟦ le ⟧ᵂ) -> B' x ≤ B x)
       -> A ≥Π B' ≤ A ≥Π B
  Σ≤Σ : ∀ {α β' β} {A : Type α}
          {B' : ᵀ⟦ A ⟧ -> Type β'}
          {B  : ᵀ⟦ A ⟧ -> Type β }
      -> (∀ x -> B' x ≤ B x)
      -> ᵀΣ A B' ≤ ᵀΣ A B
  L≤L : ∀ {α' α ′α} {α'≤′α : α' ≤ℓ ′α} {α≤′α : α ≤ℓ ′α} {A' : Type α'} {A : Type α}
      -> A' ≤ A -> Lift {α = ′α} {α'≤′α} A' ≤ Lift {α = ′α} {α≤′α} A

≤-refl  unit    = ⊤≤⊤
≤-refl  ᵀℕ      = ℕ≤ℕ
≤-refl (type α) = ᵀ≤ᵀ {α'≤α = ≤ℕ-refl α}
≤-refl (A  Π B) =  Π≤Π  (λ x -> ≤-refl (B x))
≤-refl (A ℓΠ B) = ℓΠ≤ℓΠ (λ x -> ≤-refl (B x))
≤-refl (A ≥Π B) = ≥Π≥Π  (λ x -> ≤-refl (B x))
≤-refl (ᵀΣ A B) =  Σ≤Σ  (λ x -> ≤-refl (B x))
≤-refl (Lift A) = L≤L (≤-refl A)

cod-Π : ∀ {αβ' α β} {AB' : Type αβ'} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
      -> AB' ≤ A Π B 
      -> ∃ λ β'
         -> ᵀ⟦ A ⟧ -> Type β'
cod-Π (Π≤Π {B' = B'} _) = _ , B'

-- This and other similar functions are used
-- instead of just simple pattern-matching in (≤⟦_⟧)
-- to avoid forcing an argument of type (AB' ≤ A Π B) to be in whnf,
-- with Π being any of the product types.
-- Otherwise (≤⟦ le ⟧) wouldn't reduce further.
-- Similar functions are defined for (Σ) and (Lift)
_Π·_ : ∀ {αβ' α β} {AB' : Type αβ'} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
     -> (le-Π : AB' ≤ A Π B)
     -> (x : ᵀ⟦ A ⟧)
     -> proj₂ (cod-Π le-Π) x ≤ B x
Π≤Π B'≤B Π· x = B'≤B x

cod-ℓΠ : ∀ {αβ' α} {AB' : Type αβ'} {A : Type α}
           {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
       -> AB' ≤ A ℓΠ B
       -> ∃ λ (k' : ᵀ⟦ A ⟧ -> level)
          -> (x : ᵀ⟦ A ⟧) -> Type (k' x)
cod-ℓΠ (ℓΠ≤ℓΠ {B' = B'} _) = _ , B'

_ℓΠ·_ : ∀ {αβ' α} {AB' : Type αβ'} {A : Type α}
          {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
      -> (le-ℓΠ : AB' ≤ A ℓΠ B)
      -> (x : ᵀ⟦ A ⟧)
      -> proj₂ (cod-ℓΠ le-ℓΠ) x ≤ B x
ℓΠ≤ℓΠ B'≤B ℓΠ· x = B'≤B x

cod-≥Π : ∀ {αβ' α} {AB' : Type αβ'} {A : Type α}
           {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
           {B : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le)}
       -> AB' ≤ A ≥Π B
       -> ∃ λ (k' : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level)
          -> ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k' le)
cod-≥Π (≥Π≥Π {B' = B'} _) = _ , B'

_≥Π·_ : ∀ {αβ' α' α} {AB' : Type αβ'} {A' : Type α'} {A : Type α} {le : A' ≤ A}
          {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
          {B : ∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le)}
      -> (le-≥Π : AB' ≤ A ≥Π B)
      -> (x : ≤⟦ le ⟧ᵂ)
      -> proj₂ (cod-≥Π le-≥Π) x ≤ B x
≥Π≥Π B'≤B ≥Π· x = B'≤B x

proj₂-ᵀΣ : ∀ {αβ' α β} {AB' : Type αβ'} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
         -> AB' ≤ ᵀΣ A B 
         -> ∃ λ β'
            -> ᵀ⟦ A ⟧ -> Type β'
proj₂-ᵀΣ (Σ≤Σ {B' = B'} _) = _ , B'

_Σ·_ : ∀ {αβ' α β} {AB' : Type αβ'} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
     -> (le-Σ : AB' ≤ ᵀΣ A B)
     -> (x : ᵀ⟦ A ⟧)
     -> proj₂ (proj₂-ᵀΣ le-Σ) x ≤ B x
Σ≤Σ B'≤B Σ· x = B'≤B x

L≤L-∃ : ∀ {lα' α ′α} {α≤′α : α ≤ℓ ′α} {LA' : Type lα'} {A : Type α}
      -> LA' ≤ Lift {α = ′α} {α≤′α} A -> ∃ Type
L≤L-∃ (L≤L {A' = A'} _) = _ , A'

unL≤L : ∀ {lα' α ′α} {α≤′α : α ≤ℓ ′α} {LA' : Type lα'} {A : Type α}
      -> (le-L : LA' ≤ Lift {α = ′α} {α≤′α} A) -> proj₂ (L≤L-∃ le-L) ≤ A
unL≤L (L≤L le) = le

≤⟦_⟧      {A = unit}    _    = ⊤
≤⟦_⟧      {A = ᵀℕ}     _     = ℕ
-- (A' : Type α'), (A' ≤ type α)
-- If (A' ≡ prop)    , then the result is (Type -1) (or simply (ᵀProp)) and (α' ≡ ᴺ 0).
-- If (A' ≡ type α''), then the result is (Type α'') and (α' ≡ ᴺ (suc α'')).
-- Since (predᴺ (ᴺ 0) ≡ -1) and (predᴺ (ᴺ (suc α)) ≡ ᴺ α),
-- the result is simply (Type (predᴺ α')).
≤⟦_⟧ {α'} {A = type _} _     = Type# (pred# α')
≤⟦_⟧      {A = A  Π _} le-Π  = (x : ᵀ⟦ A ⟧)   -> ≤⟦ le-Π   Π· x ⟧
≤⟦_⟧      {A = A ℓΠ _} le-ℓΠ = (x : ᵀ⟦ A ⟧)   -> ≤⟦ le-ℓΠ ℓΠ· x ⟧
≤⟦_⟧      {A = A ≥Π _} le-≥Π = ∀ {α'} {A' : Type α'} {le : A' ≤ A} ->
                               (x : ≤⟦ le ⟧ᵂ) -> ≤⟦ le-≥Π ≥Π· x ⟧
≤⟦_⟧      {A = ᵀΣ A B} le-Σ  = Σ ᵀ⟦ A ⟧ λ x    -> ≤⟦ le-Σ   Σ· x ⟧
≤⟦_⟧      {A = Lift _} le-L  = ≤⟦ unL≤L le-L ⟧

ᵀcoerce : ∀ {α' α} {A' : Type α'} {A : Type α} -> ᵀ⟦ A' ⟧ -> A' ≤ A -> ᵀ⟦ A ⟧
ᵀcoerce  _       ⊤≤⊤                = _
ᵀcoerce  n       ℕ≤ℕ                = n
ᵀcoerce  T      (ᵀ≤ᵀ {α'≤α = α'≤α}) = Lift {α'≤α = α'≤α} T
ᵀcoerce  f      ( Π≤Π  B'≤B)        = λ x -> ᵀcoerce (f x) (B'≤B x)
ᵀcoerce  f      (ℓΠ≤ℓΠ B'≤B)        = λ x -> ᵀcoerce (f x) (B'≤B x)
ᵀcoerce  f      (≥Π≥Π  B'≤B)        = λ x -> ᵀcoerce (f x) (B'≤B x)
ᵀcoerce (x , P) ( Σ≤Σ  B'≤B)        = x , ᵀcoerce P (B'≤B x)
ᵀcoerce  T      (L≤L   A'≤A)        = ᵀcoerce T A'≤A
