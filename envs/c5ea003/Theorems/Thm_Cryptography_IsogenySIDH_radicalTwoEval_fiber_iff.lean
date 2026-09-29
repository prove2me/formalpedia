-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_radicalTwoEval_fiber_iff
-- name    : Cryptography.IsogenySIDH.radicalTwoEval_fiber_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:00.091489+00:00
-- url     : https://prove2.me/theorems/46567f86-5004-4adb-b9f0-a6236a2aff19
-- title:
--   Away from `x² = 1`, equality of complete affine quotient outputs has
-- statement:
--   Away from `x² = 1`, equality of complete affine quotient outputs has
--   exactly two explanations: the input points coincide, or one is the explicit
--   deck transform of the other.  This is the exact unramified fiber theorem for
--   the rational degree-two map.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.radicalTwoEval_fiber_iff{x y z w : K}
--       (hx : x ≠ 0) (hz : z ≠ 0) (hbranch : x ^ 2 ≠ 1) :
--       radicalTwoEval (x, y) = radicalTwoEval (z, w) ↔
--         (z = x ∧ w = y) ∨ (z = x⁻¹ ∧ w = -(y * x⁻¹ ^ 2)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean#L49

-- Thm stub generated from Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
/-
# Exact fibers of the radical Montgomery 2-isogeny

This file strengthens `RadicalMontgomery` from correctness and an
`X`-coordinate fiber calculation to a classification of the complete affine
fibers away from the kernel and ramification locus.  The nontrivial point in a
fiber is the explicit deck transform

`(x,y) ↦ (x⁻¹, -(y*x⁻²))`.

The results also verify that this transform preserves the source Montgomery
curve and is an involution wherever the rational formulas are defined.
-/

open Cryptography.IsogenySIDH


variable {K : Type*} [Field K]

theorem Cryptography.IsogenySIDH.radicalTwoEval_fiber_iff{x y z w : K}
    (hx : x ≠ 0) (hz : z ≠ 0) (hbranch : x ^ 2 ≠ 1) :
    radicalTwoEval (x, y) = radicalTwoEval (z, w) ↔
      (z = x ∧ w = y) ∨ (z = x⁻¹ ∧ w = -(y * x⁻¹ ^ 2)) := by sorry
