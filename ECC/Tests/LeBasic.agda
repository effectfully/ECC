module ECC.Tests.LeBasic where

open import ECC.Types.Basic
  renaming (Type to Universe; type to universe; Typeᴺ to Type; typeᴺ to type)
open import ECC.Terms.LeBasic

ᵀI : Type 3
ᵀI = type 2 ≥Π λ A -> el A ⟶ el A 

I : Term ᵀI
I = ≥⇧ λ A -> ⇧ λ x -> ↑ x

test-1 : Term ᵀℕ
test-1 = I ≥· (↑ _ ∈̃ ᵀ≤ᵀ) · plain 0

ᵀA : Type 3
ᵀA = type 2
     ≥Π λ A -> (el A ⟶ type 2)
     ≥Π λ B -> (el A Π el B)
      Π λ f -> el A
      Π λ x -> el B x

A : Term ᵀA
A = ≥⇧ λ A -> ≥⇧ λ B -> ⇧ λ f -> ⇧ λ x -> ↑ f · ↑ x

test-2 : Term ᵀℕ
test-2 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · plain 0

test-3 : Term (type 0)
test-3 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · ↓ ᵀℕ

test-4 : Term (type 1)
test-4 = A
      ≥· (↓ _ ∈̃ ᵀ≤ᵀ)
      ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ)
       · (I ≥· (↓ _ ∈̃ ᵀ≤ᵀ))
       · ↓ (type 0)

iI : ∀ {α} {α≤3 : α ≤ℕ 3} {A : ≤⟦ ᵀ≤ᵀ {α} {α'≤α = α≤3} ⟧ᵂ} -> Term (el A ⟶ el A)
iI {α≤3 = α≤3} = I ≥· ↓ _ ∈̃ ᵀ≤ᵀ {α'≤α = α≤3}

test-i1 : Term ᵀℕ
test-i1 = iI · plain 0

ᵀiA : Set
ᵀiA = ∀ {α β} {α≤3 : α ≤ℕ 3} {β≤3 : β ≤ℕ 3} {A : ≤⟦ ᵀ≤ᵀ {α} {α'≤α = α≤3} ⟧ᵂ}
      {B : ≤⟦ (Π≤Π {A = el A} λ _ -> ᵀ≤ᵀ {β} {α'≤α = β≤3}) ⟧ᵂ}
    -> Term ((el A Π el B) ⟶ el A Π el B)

iA : ᵀiA
iA {α≤3 = α≤3} {β≤3} = A ≥· (↓ _ ∈̃ ᵀ≤ᵀ {α'≤α = α≤3})
                         ≥· ((⇧ λ _ -> ↓ _) ∈̃ Π≤Π λ _ -> ᵀ≤ᵀ {α'≤α = β≤3})

test-i2 : Term ᵀℕ
test-i2 = iA · iI · plain 0

test-i3 : Term (type 0)
test-i3 = iA · iI · ↓ ᵀℕ

test-i4 : Term (type 1)
test-i4 = iA · iI · ↓ (type 0)
