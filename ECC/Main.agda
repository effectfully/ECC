module ECC.Main where

open import ECC.Types.Basic         public
  renaming (Type to AnyType; type to anytype; Typeᴺ to Type; typeᴺ to type)
open import ECC.Types.SafeUtilities public
open import ECC.Terms.Basic         public
