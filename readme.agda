module readme where

open import ECC.Main
open import Relation.Binary.PropositionalEquality

-- # ECC-in-Agda

-- This is an attempt to formalize [An Extended Calculus of Constructions]
-- (citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.40.5883) in Agda.
-- The development contains an impredicative universe, the `unit` type, that lies in it,
-- natural numbers, infinite universe hierarchy, indexed by natural numbers,
-- Sigma and Pi types, a bounded dependent quantifier
-- and explicit liftings in the style of Agda's `Lift`, `lift` and `lower`,
-- which are used to make the subsumption rule admissible.

-- ## A quick taste

-- Here is the `I` combinator:

-- ```
I : Term (type 0 Π λ A -> A ⟶ A)
I = ⇧ λ _ -> ⇧ λ x -> ↑ x
-- ```

-- Agda's `λ` is used as a binder, so the development doesn't contain De Bruijn indicies.

-- `Π` is an infix operator. `⟶` is a non-dependent version of `Π`.

-- `⇧` is a constructor of the `Term` datatype, that being applied to a function of type
-- `(x : ᵀ⟦ A ⟧) -> Term (B x)` returns a `Term (A Π B)` modulo wrapping-unwrapping.

-- All semantic brackets like `ᵀ⟦_⟧` is functions from the defined datatypes to
-- what they denote. For example we could define

-- ```
-- ᵀ⟦_⟧ : ∀ {α} -> Type α -> Set
-- ...
-- ᵀ⟦ unit  ⟧ = ⊤
-- ᵀ⟦ A Π B ⟧ = (x : ᵀ⟦ A ⟧) -> ᵀ⟦ B x ⟧
-- ...
-- ```

-- (but `ᵀ⟦_⟧` is defined isomorphically in terms of more generic `≤⟦_⟧`).

-- The `↑` constructor makes a `Term` from a plain Agda value (like `0` for example),
-- a bound variable or a type (like `unit` for example), modulo wrapping again.

-- Another common example is the `S` combinator:

-- ```
S : Term (type 0 Π λ A -> (A ⟶ type 0) Π λ B -> (A Π λ x -> B x ⟶ type 0) Π λ C ->
      (A Π λ x -> B x Π λ y -> C x y) ⟶ (A Π λ x -> B x) Π λ g -> A Π λ x -> C x (g x))
S = ⇧ λ _ -> ⇧ λ _ -> ⇧ λ _ -> ⇧ λ f -> ⇧ λ g -> ⇧ λ x -> ↑ f · ↑ x · (↑ g · ↑ x)
-- ```

-- `_·_` is a dependent function application with the usual semantics.

-- ## Basic types

-- Here is how the `level` datatype is defined:

-- ```
-- data level : Set where
--   # : ℕ -> level
--   ω : level
-- ```

-- The `#` constructor lifts a `ℕ` into a `level`. `ω` doesn't matter fow now.

-- The relevant part of the `Type` definition is

-- ```
-- data Type : level -> Set

-- Propᵀ : Set
-- Propᵀ = Type (# 0)

-- Typeᴺ : ℕ -> Set
-- Typeᴺ = Type ∘ # ∘ suc

-- data Type where
--   unit : Propᵀ
--   ᵀℕ : Typeᴺ 0
--   type : ∀ α -> Typeᴺ α
--   _Π_ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Type β) -> Type (α ⊔ᵢ β)
-- ```

-- The impredicative universe is incorporated into the predicative one:

-- ```
-- type 0 : Type (# 1)
-- type 1 : Type (# 2)
-- ...
-- type i : Type (# (suc i))
-- ```

-- and

-- ```
-- prop : Typeᴺ 0
-- prop = type 0

-- typeᴺ : ∀ α -> Typeᴺ (suc α)
-- typeᴺ = type ∘ suc 
-- ```

-- A user doesn't see, that `prop` and `typeᴺ` are represented in terms of
-- the same `type` constructor, since this constructor is renamed in the `ECC.Main` module
-- to `anytype` and `typeᴺ` is renamed to `type`.

-- With this representation you don't need this three rules for subtyping:

-- ```
-- prop ≤ prop
-- ∀ α -> prop ≤ type α
-- ∀ α' α -> α' ≤ℕ α -> type α' ≤ type α
-- ```

-- just the last one. It's also crucial for unification to have only one rule.

-- One another option is to extend the `ℕ` datatype with the `-1` constant
-- and to defined `prop = type -1` in the style of HoTT, but this breaks unification again.

-- `ECC.Main` also renames `Type` to `AnyType` and `Typeᴺ to Type`. Let's do some tests:

-- ```
test-2 : Propᵀ
test-2 = unit

test-3 : Type 0
test-3 = ᵀℕ

test-4 : Type 1
test-4 = type 0
-- ```

-- The `_Π_` constructor is defined in terms of induction-recursion:

-- ```
-- _Π_ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Type β) -> Type (α ⊔ᵢ β)
-- ```

-- `⟶` is a non-dependent version of `_Π_`:

-- ```
-- _⟶_  : ∀ {α β} -> Type α -> Type β -> Type (α ⊔ᵢ β)
-- A  ⟶ B = A  Π λ _ -> B
-- ```

-- Random tests again:

-- ```
test-5 : Propᵀ -- impredicativity here
test-5 = type 0 ⟶ unit

test-6 : Type 2
test-6 = (type 1 Π λ A -> A) ⟶ ᵀℕ ⟶ type 0
-- ```

-- Recall that `ᵀ⟦_⟧` maps a value to its meaning:

-- ```
test-7 : ᵀ⟦ ᵀℕ ⟧ ≡ ℕ
test-7 = refl

test-8 : ᵀ⟦ prop ⟧ ≡ Propᵀ
test-8 = refl

test-9 : ∀ α -> ᵀ⟦ type α ⟧ ≡ Type α
test-9 _ = refl

test-10 : ∀ α -> Type (suc α)
test-10 α = type α
-- ```

-- The last two examples show predicativity of the system.
-- `type α : Type (suc α)` and `type α` evaluates to `Type α`,
-- hence `Type α` is of type `Type (suc α)`.

-- ## Tagging

-- This datatype:

-- ```
-- record Tag {α β} {A : Set α} (B : (x : A) -> Set β) (x : A) : Set (α ⊔ β) where
--   constructor tag
--   field el : B x
-- open Tag public

-- tagWith : ∀ {α β} {A : Set α} {B : (x : A) -> Set β} -> (x : A) -> B x -> Tag B x
-- tagWith _ = tag
-- ```

-- is used pretty everywhere in the code. An example from the `ECC.Types.Level` module:

-- ```
-- _≤ℕ_ : ℕ -> ℕ -> Set
-- 0     ≤ℕ _     = ⊤
-- suc _ ≤ℕ 0     = ⊥
-- suc n ≤ℕ suc m = n ≤ℕ m 

-- _≤ℕᵂ_ : ℕ -> ℕ -> Set
-- n ≤ℕᵂ m = Tag (uncurry _≤ℕ_) (n , m)

-- _⊔̂ℕᵢ_ : ∀ {n m p} -> n ≤ℕᵂ p -> m ≤ℕᵂ p -> n ⊔ℕᵢ m ≤ℕᵂ p
-- _⊔̂ℕᵢ_ {n} {m} (tag n≤p) (tag m≤p) = tag (⊔ℕᵢ-≤ℕ n {m} n≤p m≤p)
-- ```

-- `_≤ℕ_` is not a datatype ─ it's a function, so Agda can't infer `n` from `n ≤ℕ m`
-- (she often can infer `m`, if `n` is known, but it's easier to just tag everything).
-- If we define `_⊔̂ℕᵢ_` like

-- ```
-- _⊔̂ℕᵢ_ : ∀ {n m p} -> n ≤ℕ p -> m ≤ℕ p -> n ⊔ℕᵢ m ≤ℕ p
-- ```

-- then we would need to explicitly pass `n` and `m` to every call to `_⊔̂ℕᵢ_`.
-- A common tactic in this case is to wrap `_≤ℕ_` in an ad hoc record datatype,
-- but I like this generic approach with tags more.

-- ## Basic terms

-- The relevant part of the `Term` definition is

-- ```
-- data Term : ∀ {α} -> Type α -> Set where
--   ↑ : ∀ {α} {A : Type α} -> ᵀ⟦ A ⟧ᵂ -> Term A
--   ⇧ : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
--     -> ((x : ᵀ⟦ A ⟧ᵂ) -> Term (B (el x)))
--     -> Term (A Π B)
--   _·_ : ∀ {α β} {A : Type α} {B : ᵀ⟦ A ⟧ -> Type β}
--       -> Term (A Π B) -> (x : Term A) -> Term (B ⟦ x ⟧)

-- ⟦_⟧ : ∀ {α} {A : Type α} -> Term A -> ᵀ⟦ A ⟧
-- ⟦ ↑ x      ⟧ = el x
-- ⟦  ⇧ f     ⟧ = λ x -> ⟦ f (tag x) ⟧
-- ⟦ f  · x   ⟧ = ⟦ f ⟧ ⟦ x ⟧
-- ```

-- `ᵀ⟦_⟧ᵂ` is a tagged version of `ᵀ⟦_⟧`.
-- There is induction-recursion again ─ in the definition of `_·_`.
-- This all is a usual dependently typed stuff.

-- Two auxuliary functions (the first is the special case of the second),
-- that make `Terms` from plain Agda values are:

-- ```
-- -- That's how we get types at the value level.
-- ↓ : ∀ {α} -> Type (# α) -> Term (type α)
-- ↓ = ↑ ∘ tag

-- plain : ∀ {α} {A : Type α} -> ᵀ⟦ A ⟧ -> Term A
-- plain = ↑ ∘ tag
-- ```

-- A couple of basic examples:

-- ```
test-11 : Term unit
test-11 = plain tt

test-12 : Term prop
test-12 = ↓ unit
-- ```

-- The `A` combinator (`_$_` in Agda and Haskell) is

-- ```
A : Term (type 0
          Π λ A -> (A ⟶ type 0)
          Π λ B -> (A Π B)
          Π λ f -> A
          Π λ x -> B x)
A = ⇧ λ _ -> ⇧ λ _ -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x
-- ```

-- We can encode `id $ 0` as follows:

-- ```
test-13 : Term ᵀℕ
test-13 = A · ↑ _ · ↑ _ · (I · ↑ _) · plain 0
-- ```

-- It's also possible to use Agda's implicit arguments to remove these `↑ _`,
-- but it doesn't matter for now.

-- It is straightforward to define Church-encoded lists:

-- ```
List : Type 0 -> Type 1
List A = type 0 Π λ B -> (A ⟶ B ⟶ B) ⟶ B ⟶ B

nil : Term (type 0 Π λ A -> List A)
nil = ⇧ λ A -> ⇧ λ B -> ⇧ λ f -> ⇧ λ z -> ↑ z

foldr : Term (type 0 Π λ A -> type 0 Π λ B -> (A ⟶ B ⟶ B) ⟶ B ⟶ List A ⟶ B)
foldr = ⇧ λ A -> ⇧ λ B -> ⇧ λ f -> ⇧ λ z -> ⇧ λ xs -> ↑ xs · ↑ B · ↑ f · ↑ z

cons : Term (type 0 Π λ A -> A ⟶ List A ⟶ List A)
cons = ⇧ λ A -> ⇧ λ x -> ⇧ λ xs -> ⇧ λ B -> ⇧ λ f -> ⇧ λ z ->
  ↑ f · ↑ x · (foldr · ↑ A · ↑ B · ↑ f · ↑ z · ↑ xs)

sum : Term (List ᵀℕ ⟶ ᵀℕ)
sum = foldr · ↑ _ · ↑ _ · plain _+_ · plain 0

test-14 : ⟦ sum · (cons · ↑ _ · plain 1 ·
                  (cons · ↑ _ · plain 2 · 
                  (cons · ↑ _ · plain 3 ·
                  (nil · ↑ _)))) ⟧ ≡ 6
test-14 = refl
-- ```

-- ## Universe polymorphism

-- One another constructor of the `Type` datatype is

-- ```
-- _ℓΠ_ : ∀ {α} (A : Type α) {k : ᵀ⟦ A ⟧ -> level} -> (∀ x -> Type (k x)) -> Typeω
-- ```

-- Recall, how `_Π_` is defined:

-- ```
-- _Π_ : ∀ {α β} -> (A : Type α) -> (ᵀ⟦ A ⟧ -> Type β) -> Type (α ⊔ᵢ β)
-- ```

-- So in `A ℓΠ λ x -> B x` a universe, where `B x` lies, depends on a value of type `A`.
-- `Typeω` is a synonym for `Type ω`. This is just like in Agda.
-- For example C-c C-d `∀ α -> Set α` gives this error:

-- ```
-- 1,3-13
-- Setω is not a valid type
-- when checking that the expression ∀ α → Set α has type _690
-- ```

-- However there is no error in this development
-- (I don't quite understand, why it appears in Agda):

-- ```
test-15 : Typeω
test-15 = ᵀℕ ℓΠ λ α -> type α
-- ```

-- The `Term` datatype contains corresponding constructors for
-- universe polymorphic function application and universe polymorphic lambda abstraction:

-- ```
-- ℓ⇧ : ∀ {α} {A : Type α} {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
--    -> ((x : ᵀ⟦ A ⟧ᵂ) -> Term (B (el x)))
--    -> Term (A ℓΠ B)
-- _ℓ·_ : ∀ {α} {A : Type α} {k : ᵀ⟦ A ⟧ -> level} {B : (x : ᵀ⟦ A ⟧) -> Type (k x)}
--      -> Term (A ℓΠ B) -> (x : Term A) -> Term (B ⟦ x ⟧)
-- ```

-- It is straightforward to make the universe polymorphic `I` and `A` combinators:

-- ```
uI : Term (ᵀℕ ℓΠ λ α -> type α Π λ A -> A ⟶ A)
uI = ℓ⇧ λ α -> ⇧ λ A -> ⇧ λ x -> ↑ x

uA : Term (ᵀℕ
          ℓΠ λ α -> ᵀℕ
          ℓΠ λ β -> type α
           Π λ A -> (A ⟶ type β)
           Π λ B -> (A Π B)
           Π λ f -> A
           Π λ x -> B x)
uA = ℓ⇧ λ α -> ℓ⇧ λ β -> ⇧ λ A -> ⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x
-- ```

-- This term corresponds to `id $ 0`

-- ```
test-16 : Term ᵀℕ
test-16 = uA ℓ· ↑ _ ℓ· ↑ _ · ↑ _ · ↑ _ · (uI ℓ· ↑ _ · ↑ _) · plain 0 
-- ```

-- This term corresponds to `id $ ℕ`

-- ```
test-17 : Term (type 0)
test-17 = uA ℓ· ↑ _ ℓ· ↑ _ · ↑ _ · ↑ _ · (uI ℓ· ↑ _ · ↑ _) · ↓ ᵀℕ
-- ```

-- This term corresponds to `id $ Set`

-- ```
test-18 : Term (type 1)
test-18 = uA ℓ· ↑ _ ℓ· ↑ _ · ↑ _ · ↑ _ · (uI ℓ· ↑ _ · ↑ _) · ↓ (type 0)
-- ```

-- For a more complicated example see the `ECC.Tests.UniversePolymorphism` module.

-- ## Subtyping

-- Here is the bounded dependent quantifier:

-- ```
-- _≥Π_ : ∀ {α}
--      -> (A : Type α) {k : ∀ {α'} {A' : Type α'} -> A' ≤ A -> level}
--      -> (∀ {α'} {A' : Type α'} {le : A' ≤ A} -> ≤⟦ le ⟧ᵂ -> Type (k le))
--      -> Type (α ⊔ᵢ k (≤-refl A))
-- ```

-- Roughly, in `A ≥Π B` `B` receives a value of type `ᵀ⟦ A' ⟧`
-- for all `A'`, such that `A' ≤ A`.
-- However if we define `_≥Π_` in terms of `ᵀ⟦_⟧`, we would need to pattern-match on `A'`,
-- which is universally quantified and hence unknown. That would make unification stuck.
-- For example (remember, that `Type` was renamed to `AnyType`):

-- ```
postulate
  _≥Π'_ : ∀ {α}
        -> (A : AnyType α) {k : ∀ {α'} {A' : AnyType α'} -> A' ≤ A -> level}
        -> (∀ {α'} {A' : AnyType α'} {le : A' ≤ A} -> ᵀ⟦ A' ⟧ -> AnyType (k le))
        -> AnyType (α ⊔ᵢ k (≤-refl A))

-- test-19 : Type 1
-- test-19 = type 0 ≥Π' λ A -> {!!}
-- ```

-- The type of the hole is `AnyType (_k_1034 .le)`. `A` in the hole has type `ᵀ⟦ .A' ⟧`.
-- So we can't fill the hole with `A`. But we know, that `A` is of type `AnyType α`
-- for some `α`, since the only rule, that matches the `A' ≤ type α` pattern
-- is `type α' ≤ type α`, and `type α'` evaluates to `AnyType α'`.
-- But with the definition, that uses `≤⟦_⟧`, there no such problem:

-- ```
test-19-ok : Type 1
test-19-ok = type 0 ≥Π λ A -> el A
-- ```

-- Subtyping rules for basic cases are

-- ```
-- data _≤_ : ∀ {α' α} -> Type α' -> Type α -> Set where
--   ⊤≤⊤ : unit ≤ unit
--   ℕ≤ℕ : ᵀℕ ≤ ᵀℕ
--   ᵀ≤ᵀ : ∀ {α' α} {α'≤α : α' ≤ℕ α} -> type α' ≤ type α
--   Π≤Π : ∀ {α β' β} {A : Type α}
--           {B' : ᵀ⟦ A ⟧ -> Type β'}
--           {B  : ᵀ⟦ A ⟧ -> Type β }
--       -> (∀ x -> B' x ≤ B x)
--       -> A Π B' ≤ A Π B
-- ```

-- There is no contravariance in the `Π≤Π` constructor.

-- Here is how `≤⟦_⟧` defined for two trivial cases:

-- ```
-- ≤⟦_⟧ : ∀ {α' α} {A' : Type α'} {A : Type α} -> A' ≤ A -> Set
-- ≤⟦_⟧      {A = unit  } _     = ⊤
-- ≤⟦_⟧      {A = ᵀℕ    } _     = ℕ
-- ```

-- If `A' ≤ unit`, then `A' ≡ unit`, and `A'` evaluates to `⊤`.
-- If `A' ≤ ᵀℕ  `, then `A' ≡ ᵀℕ  `, and `A'` evaluates to `ℕ`.

-- More interesting case is

-- ```
-- ≤⟦_⟧ {α'} {A = type _} _     = Type (# (pred# α'))
-- ```

-- With `pred#` being

-- ```
-- pred# : level -> ℕ
-- pred# (# n) = pred n
-- pred#  ω    = 0 -- Satisfying the totality checker
-- ```

-- I.e. if `A' : Type α'` and `A' ≤ type α`, then `A' ≡ type (pred# α')`
-- due to the predicativity. Here is a proof (with the renamings):

-- ```
module mproof-1 where
  open import Relation.Binary.HeterogeneousEquality
  proof-1 : ∀ {α' α} {A' : AnyType α'} -> A' ≤ anytype α -> A' ≅ anytype (pred# α')
  proof-1 ᵀ≤ᵀ = refl
-- ```

-- And for the product type `≤⟦_⟧` is

-- ```
-- ≤⟦_⟧      {A = A  Π _} le-Π  = (x : ᵀ⟦ A ⟧)   -> ≤⟦ le-Π   Π· x ⟧
-- ```

-- `Π·` has complicated type, but its definition is simple:

-- ```
-- Π≤Π B'≤B Π· x = B'≤B x
-- ```

-- We cannot just write

-- ```
-- ≤⟦_⟧      {A = A  Π _} (Π≤Π B'≤B)  = (x : ᵀ⟦ A ⟧)   -> ≤⟦ B'≤B · x ⟧
-- ```

-- since it would force an argument of `≤⟦_⟧` to be in head weak normal form,
-- making `≤⟦ le ⟧` stuck, when `le` is not in whnf.
