-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_radicalTwoEval_exact_two_fiber
-- name    : Cryptography.IsogenySIDH.radicalTwoEval_exact_two_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:43:52.066425+00:00
-- url     : https://prove2.me/theorems/83bc9421-a1ba-46a7-ab16-992a6ed849e3
-- title:
--   On a source-curve point away from poles and ramification, the complete
-- statement:
--   On a source-curve point away from poles and ramification, the complete
--   fiber consists precisely of the point and its distinct deck mate, and both
--   points remain on the source curve.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.radicalTwoEval_exact_two_fiber{A x y z w : K}
--       (hx : x ≠ 0) (hbranch : x ^ 2 ≠ 1)
--       (hP : OnMontgomery A (x, y)) (hz : z ≠ 0) :
--       (OnMontgomery A (radicalTwoDeck (x, y)) ∧
--         radicalTwoDeck (x, y) ≠ (x, y)) ∧
--       (radicalTwoEval (z, w) = radicalTwoEval (x, y) ↔
--         (z, w) = (x, y) ∨ (z, w) = radicalTwoDeck (x, y)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean#L100

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

theorem Cryptography.IsogenySIDH.radicalTwoEval_exact_two_fiber{A x y z w : K}
    (hx : x ≠ 0) (hbranch : x ^ 2 ≠ 1)
    (hP : OnMontgomery A (x, y)) (hz : z ≠ 0) :
    (OnMontgomery A (radicalTwoDeck (x, y)) ∧
      radicalTwoDeck (x, y) ≠ (x, y)) ∧
    (radicalTwoEval (z, w) = radicalTwoEval (x, y) ↔
      (z, w) = (x, y) ∨ (z, w) = radicalTwoDeck (x, y)) := by sorry
