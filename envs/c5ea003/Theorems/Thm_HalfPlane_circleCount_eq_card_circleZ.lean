-- Prove2me | Theorems.Thm_HalfPlane_circleCount_eq_card_circleZ
-- name    : HalfPlane.circleCount_eq_card_circleZ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:35:45.42749+00:00
-- url     : https://prove2.me/theorems/e4a17001-ad1a-4dd1-8555-a0d6cd7ce807
-- title:
--   The natural-number model and the `ZMod` model of the circle have the same size.
-- statement:
--   The natural-number model and the `ZMod` model of the circle have the same size.
--
--   ```lean
--   theorem HalfPlane.circleCount_eq_card_circleZ(N : ℕ) [NeZero N] :
--       circleCount N = (circleZ N).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HalfPlaneCircleBasic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HalfPlaneCircleBasic.lean#L77

-- Thm stub generated from MachineLearning/HalfPlaneCircleBasic.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic

/-!
# The half-plane circle count: basic definitions

For a modulus `N` we study the *modular circle*

  `Circle(N) = {(x, y) ∈ [0,N)² : x² + y² ≡ 1 (mod N)}`

together with the **non-CRT-separable** half-plane cut `x + y < N/2`
(the sum `x + y` is taken as an *integer*, not modulo `N`, which is exactly
what destroys separability).

This file sets up:

* `circleFinset N`  — the circle as a finite set of pairs of naturals,
* `circleCount N`   — its cardinality `C(N)`,
* `halfPlaneCount N`— the count `H(N)` of circle points in the low half-plane
  `2(x+y) < N`,
* `highCount N`     — the count of circle points with `2(x+y) > 3N`,
* `unitRootCount N` — the number of square roots of `1` below `N/2`,

and the bridge to the algebraic description of the circle inside `ZMod N`,
which is what makes the Chinese Remainder analysis possible.
-/

open HalfPlane

open Finset








variable {N : ℕ}

theorem HalfPlane.circleCount_eq_card_circleZ(N : ℕ) [NeZero N] :
    circleCount N = (circleZ N).card := by sorry
