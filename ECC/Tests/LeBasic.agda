module ECC.Tests.LeBasic where

open import ECC.Types.Basic
  renaming (Type to AnyType; type to anytype; Typeᴺ to Type; typeᴺ to type)
open import ECC.Terms.LeBasic

ᵀI : Type 3
ᵀI = type 2 ≥Π λ A -> el A ⟶ el A 

I : Term ᵀI
I = ≥⇧ λ A -> ⇧ λ x -> ↑ x

test-1 : Term ᵀℕ
test-1 = I ≥· (↓ _ ∈̃ ᵀ≤ᵀ) · plain 0

ᵀA : Type 3
ᵀA = type 2
     ≥Π λ A -> (el A ⟶ type 2)
     ≥Π λ B -> (el A Π el B)
      Π λ f -> el A
      Π λ x -> el B x

A : Term ᵀA
A = ≥⇧ λ A -> ≥⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x

test-5 : Term ᵀℕ
test-5 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · plain 0

test-6 : Term (type 0)
test-6 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · ↓ ᵀℕ

test-7 : Term (type 1)
test-7 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · ↓ (type 0)
