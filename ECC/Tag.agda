module ECC.Tag where

open import Level

-- (Tag B x) contains an element of type (B x),
-- but it's also always possible to infer (x) from (Tag B x),
-- while it's not always possible to infer (x) from (B x).
record Tag {α β} {A : Set α} (B : (x : A) -> Set β) (x : A) : Set (α ⊔ β) where
  constructor tag
  field el : B x
open Tag public

-- Explicit tagging.
tagWith : ∀ {α β} {A : Set α} {B : (x : A) -> Set β} -> (x : A) -> B x -> Tag B x
tagWith _ = tag

uncurryᵂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ} {x : A}
         -> ((x : A) -> (y : B x) -> C y) -> (ty : Tag B x) -> C (el ty)
uncurryᵂ g (tag y) = g _ y

_<ᵂ>_ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ} {x : A}
      -> (f : ∀ {x} -> (y : B x) -> C y) -> (ty : Tag B x) -> Tag C (el ty)
g <ᵂ> tag y = tag (g y)
