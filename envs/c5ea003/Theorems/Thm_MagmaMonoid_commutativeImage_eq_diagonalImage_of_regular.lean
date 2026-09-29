-- Prove2me | Theorems.Thm_MagmaMonoid_commutativeImage_eq_diagonalImage_of_regular
-- name    : MagmaMonoid.commutativeImage_eq_diagonalImage_of_regular
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:12.880838+00:00
-- url     : https://prove2.me/theorems/0898d67a-3ba8-42fd-9813-02d161b43de6
-- title:
--   Regularity forces every diagonal point in the full pairmorph image to already
-- statement:
--   Regularity forces every diagonal point in the full pairmorph image to already
--   occur as the image of a diagonal input (the forward implication of Proposition 24).
--
--   ```lean
--   theorem MagmaMonoid.commutativeImage_eq_diagonalImage_of_regular{X : Type*}
--       (f : Operation X) (h : IsRegular f) :
--       commutativeImage f = diagonalImage f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/MagmaMonoid/Transformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/MagmaMonoid/Transformation.lean#L147

-- Thm stub generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid

theorem MagmaMonoid.commutativeImage_eq_diagonalImage_of_regular{X : Type*}
    (f : Operation X) (h : IsRegular f) :
    commutativeImage f = diagonalImage f := by sorry
