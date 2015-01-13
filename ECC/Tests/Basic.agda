module ECC.Tests.Basic where

open import ECC.Terms.Basic
open import ECC.Types.Utilities

ᵀtest-0 : Typeω
ᵀtest-0 = ᵀℕ ℓΠ type

ᵀtest-1 : Typeᴺ 3
ᵀtest-1 = type 2
          ≥Π λ A -> (el A ⟶ el A)
           Π λ f -> el A
           Π λ x -> el A

test-1 : Term ᵀtest-1
test-1 = ≥⇧ λ A -> ⇧ λ f -> ⇧ λ x -> ↑ f · (↑ f · ↑ x)

ᵀI : Typeᴺ 3
ᵀI = type 2 ≥Π λ A -> el A ⟶ el A 

-- The (id) function.
I : Term ᵀI
I = ≥⇧ λ A -> ⇧ λ x -> ↑ x

test-2 : Term ᵀℕ
test-2 = I ≥· ⌈ ᵀℕᵂ ⌉ · plain 0

ᵀA : Typeᴺ 3
ᵀA = type 2
     ≥Π λ A -> (el A ⟶ type 2)
     ≥Π λ B -> (el A Π el B)
      Π λ f -> el A
      Π λ x -> el B x

-- The (_$_) function.
A : Term ᵀA
A = ≥⇧ λ A -> ≥⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x

-- (id $ 0) modulo subtyping stuff.
test-5 : Term ᵀℕ
test-5 = A
      ≥· ⌈ ᵀℕᵂ ⌉
      ≥· ⌈ ᵀℕ ➘ ᵀℕᵂ ⌉
       · (I ≥· ⌈ ᵀℕᵂ ⌉)
       · plain 0

-- test-5 desugars to
test-5-desugared : Term ᵀℕ
test-5-desugared = A
      ≥· (tagWith ᵀ≤ᵀ ᵀℕ)
      ≥· (tagWith (Π≤Π λ _ -> ᵀ≤ᵀ) (λ _ -> ᵀℕ))
       · (I ≥· tagWith ᵀ≤ᵀ ᵀℕ)
       · plain 0

-- A direct equivalent of
test-5-ex : ℕ
test-5-ex = _$_ {A = ℕ} {B = λ _ -> ℕ} (id {A = ℕ}) 0

-- (id $ ᵀℕ) modulo subtyping stuff.
test-6 : Term (type 0)
test-6 = A
      ≥· ⌈ typeᵂ 0 ⌉
      ≥· ⌈ _ ➘ typeᵂ 0 ⌉
       · (I ≥· ⌈ typeᵂ 0 ⌉)
       · ↓ ᵀℕ

-- A direct equivalent of
test-6-ex : Set
test-6-ex = _$_ {A = Set} {B = λ _ -> Set} (id {A = Set}) ℕ

-- (id $ type 0) modulo subtyping stuff.
test-7 : Term (type 1)
test-7 = A
      ≥· ⌈ typeᵂ 1 ⌉
      ≥· ⌈ _ ➘ typeᵂ 1 ⌉
       · (I ≥· ⌈ typeᵂ 1 ⌉)
       · ↓ (type 0)

-- A direct equivalent of
test-7-ex : Set₁
test-7-ex = _$_ {A = Set₁} {B = λ _ -> Set₁} (id {A = Set₁}) Set

-- Note that Agda uses universe polymorphism for this kind of polymorphism,
-- but (Term) examples here use only subtyping.
-- It's also possible to write universe polymorphic code like in Agda.
