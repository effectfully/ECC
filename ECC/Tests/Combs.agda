module ECC.Tests.Combs where

open import ECC.Main

open import Relation.Binary.PropositionalEquality

module explicit where
  I : Term (type 0 Π λ A -> A ⟶ A)
  I = ⇧ λ _ -> ⇧ λ x -> ↑ x
  
  K : Term (type 0 Π λ A -> (A ⟶ type 0) Π λ B -> A Π λ x -> B x ⟶ A)
  K = ⇧ λ _ -> ⇧ λ _ -> ⇧ λ x -> ⇧ λ y -> ↑ x
  
  S : Term (type 0 Π λ A -> (A ⟶ type 0) Π λ B -> (A Π λ x -> B x ⟶ type 0) Π λ C ->
        (A Π λ x -> B x Π λ y -> C x y) ⟶ (A Π λ x -> B x) Π λ g -> A Π λ x -> C x (g x))
  S = ⇧ λ _ -> ⇧ λ _ -> ⇧ λ _ -> ⇧ λ f -> ⇧ λ g -> ⇧ λ x -> ↑ f · ↑ x · (↑ g · ↑ x)

module implicit where
  I : {A : Type 0} -> Term (A ⟶ A)
  I = ⇧ λ x -> ↑ x
  
  K : {A : Type 0} {B : ᵀ⟦ A ⟧ -> Type 0} -> Term (A Π λ x -> B x ⟶ A)
  K = ⇧ λ x -> ⇧ λ y -> ↑ x
  
  S : {A : Type 0} {B : ᵀ⟦ A ⟧ -> Type 0} {C : ∀ {x} -> ᵀ⟦ B x ⟧ -> Type 0} -> Term
        ((A Π λ x -> B x Π λ y -> C y) ⟶ (A Π λ x -> B x) Π λ g -> A Π λ x -> C (g x))
  S = ⇧ λ f -> ⇧ λ g -> ⇧ λ x -> ↑ f · ↑ x · (↑ g · ↑ x)

  I' : {A : Type 0} -> Term (A ⟶ A)
  I' = S · K · K {B = λ _ -> ᵀℕ}

  test : ∀ {A} -> ⟦ I' {A} ⟧ ≡ id
  test = refl

module both where
  module e = explicit

  I : {A : Type 0} -> Term (A ⟶ A)
  I = e.I · ↑ _
  
  K : {A : Type 0} {B : ᵀ⟦ A ⟧ -> Type 0} -> Term (A Π λ x -> B x ⟶ A)
  K = e.K · ↑ _ · ↑ _
  
  S : {A : Type 0} {B : ᵀ⟦ A ⟧ -> Type 0} {C : ∀ {x} -> ᵀ⟦ B x ⟧ -> Type 0} -> Term
        ((A Π λ x -> B x Π λ y -> C y) ⟶ (A Π λ x -> B x) Π λ g -> A Π λ x -> C (g x))
  S = e.S · ↑ _ · ↑ _ · ↑ _

  I' : {A : Type 0} -> Term (A ⟶ A)
  I' = S · K · K {B = λ _ -> ᵀℕ}

  test : ∀ {A} -> ⟦ I' {A} ⟧ ≡ id
  test = refl
