-- Prove2me | Theorems.Thm_MagmaMonoid_commutativeImage_eq_diagonalImage_of_idempotent
-- name    : MagmaMonoid.commutativeImage_eq_diagonalImage_of_idempotent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:01.815158+00:00
-- url     : https://prove2.me/theorems/4ae9a968-4410-4617-ab8d-9d8739d9b168
-- title:
--   For a magma-monoid idempotent, the diagonal image equals the diagonal part of
-- statement:
--   For a magma-monoid idempotent, the diagonal image equals the diagonal part of
--   its full pairmorph image (Proposition 22 of the paper).
--
--   ```lean
--   theorem MagmaMonoid.commutativeImage_eq_diagonalImage_of_idempotent{X : Type*}
--       (f : Operation X) (h : product f f = f) :
--       commutativeImage f = diagonalImage f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/MagmaMonoid/Transformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/MagmaMonoid/Transformation.lean#L130

-- Thm stub generated from Tropical/MagmaMonoid/Transformation.lean
import Mathlib
import Definitions.Def_Tropical_MagmaMonoid_Transformation

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

open MagmaMonoid

theorem MagmaMonoid.commutativeImage_eq_diagonalImage_of_idempotent{X : Type*}
    (f : Operation X) (h : product f f = f) :
    commutativeImage f = diagonalImage f := by sorry
