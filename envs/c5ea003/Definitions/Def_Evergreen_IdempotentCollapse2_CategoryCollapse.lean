-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_CategoryCollapse
-- name    : Evergreen_IdempotentCollapse2_CategoryCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:25.976614+00:00
-- url     : https://prove2.me/theorems/53e183bd-032f-4f84-88fe-bec9eb4cbed0
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_CategoryCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.CategoryCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/CategoryCollapse.lean by skeleton subtraction
import Mathlib

/-!
# Direction 8: Category-Theoretic Idempotents — The Karoubi Envelope

An idempotent morphism e ∘ e = e can be split: e = ι ∘ r with r ∘ ι = id.
-/

open Function Set

/-
PROBLEM
Commuting idempotents compose to an idempotent.

PROVIDED SOLUTION
e₁(e₂(e₁(e₂ x))) = e₁(e₁(e₂(e₂ x))) by hcomm applied to e₂ x = e₁(e₂(e₂ x)) by h₁ = e₁(e₂ x) by h₂. Just rewrite with hcomm, h₁, h₂ in sequence.
-/


/-
PROBLEM
eⁿ = e for n ≥ 1.

PROVIDED SOLUTION
Induction on n starting from 1. Base n=1: e^1 = e. Step: e^(n+1) = e^n * e = e * e = e by IH and he.
-/

/-- The Karoubi envelope consists of idempotent elements. -/
structure KaroubiElement (M : Type*) [Monoid M] where
  idem : M
  idem_sq : idem * idem = idem


/-
PROBLEM
Product of commuting idempotents is idempotent.

PROVIDED SOLUTION
In a CommMonoid: (a*b)*(a*b) = a*a*b*b = a*b using idem_sq for both. Use mul_comm and mul_assoc to rearrange, then a.idem_sq and b.idem_sq.
-/


