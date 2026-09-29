-- Prove2me | Theorems.Thm_MagmaMonoid_product_self_eq_iff
-- name    : MagmaMonoid.product_self_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:17.032032+00:00
-- url     : https://prove2.me/theorems/3461aed3-a721-47c5-8922-6a9a01a4ce56
-- title:
--   Idempotents are exactly the operations whose pairmorph fixes every point of its
-- statement:
--   Idempotents are exactly the operations whose pairmorph fixes every point of its
--   image (Proposition 20 of the paper).
--
--   ```lean
--   theorem MagmaMonoid.product_self_eq_iff{X : Type*} (f : Operation X) :
--       product f f = f ↔ ∀ p ∈ pairImage f, pairmorph f p = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/MagmaMonoid/Transformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/MagmaMonoid/Transformation.lean#L106

-- Thm stub generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid

theorem MagmaMonoid.product_self_eq_iff{X : Type*} (f : Operation X) :
    product f f = f ↔ ∀ p ∈ pairImage f, pairmorph f p = p := by sorry
