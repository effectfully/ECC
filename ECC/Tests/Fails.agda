module ECC.Tests.Fails where

-- A big problem is that we can't automatically get (predᴺ γ) from (predᴺ α ⊔ᵢ predᴺ β),
-- which is easy without the (prop ≤ type α) rule.
-- So we cannot pass something like (el a ⟶ el b)
-- to a function that receives an element of (Type (predᴺ γ)).
-- (subst)s in type signatures -- this doesn't look promising.
-- But we probably can explicitly turn off the (prop ≤ type α) rule, when it's needed.
