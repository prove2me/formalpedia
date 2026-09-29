-- Prove2me | Theorems.Thm_HigherPythagorean_boundary_move
-- name    : HigherPythagorean.boundary_move
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:40:29.307663+00:00
-- url     : https://prove2.me/theorems/a9837e61-7e75-454d-b37e-0faa4b789e49
-- title:
--   The reflection move acts on the ideal boundary by the affineâfractional map
-- statement:
--   The reflection move acts on the ideal boundary by the affineâfractional map
--   `u â¦ (u â s + 1)/(2 â s)`, and multiplies the height by `2 â s`.
--
--   ```lean
--   theorem HigherPythagorean.boundary_move{a b c d : ℤ} (hd : 0 < d) (hs : (a + b + c : ℤ) ≠ 2 * d) :
--       ((d - qk a b c d : ℤ) : ℚ) = (2 - shadow a b c d) * (d : ℚ) ∧
--       (((a - qk a b c d : ℤ) : ℚ)) / ((d - qk a b c d : ℤ) : ℚ) =
--         ((a : ℚ) / (d : ℚ) - shadow a b c d + 1) / (2 - shadow a b c d) := by sorry
--
--   /-! ## Algebraicity of the growth constant -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/HyperbolicBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/HyperbolicBoundary.lean#L39

-- Thm stub generated from Shared/HigherPythagorean/HyperbolicBoundary.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_HyperbolicBoundary
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The hyperbolic (ideal boundary) picture, and algebraicity of the growth constant

Normalising a null vector by its height embeds the Pythagorean quadruples into the ideal
boundary `S²` of the hyperbolic `4`-space (equivalently, the boundary sphere of the Poincaré
ball), and the reflection move acts there by an explicit affine–fractional (Möbius) formula.

* `sphere_of_quad` : a Pythagorean quadruple normalises to a rational point of the unit sphere.
* `boundary_move` : the reflection acts on the boundary by `u ↦ (u − s + 1)/(2 − s)`, where
  `s = (a+b+c)/d` is the *shadow* of the node; the height is multiplied by `2 − s`.
* `shadow_bound` : `|s| ≤ √3`, so the height multiplier `2 − s` lies in `[2−√3, 2+√3]`.
* `growth_const_quadratic` : the growth constant `(√n+1)/(√n−1)` of dimension `n` is an
  algebraic number of degree ≤ 2: it is a root of `(n−1)X² − 2(n+1)X + (n−1)`.  For `n = 2` this
  is `X²−6X+1` (root `3+2√2 = (1+√2)²`, silver ratio) and for `n = 3` it is `X²−4X+1`
  (root `2+√3`).
-/

open HigherPythagorean

/-! ## Boundary sphere -/

theorem HigherPythagorean.boundary_move{a b c d : ℤ} (hd : 0 < d) (hs : (a + b + c : ℤ) ≠ 2 * d) :
    ((d - qk a b c d : ℤ) : ℚ) = (2 - shadow a b c d) * (d : ℚ) ∧
    (((a - qk a b c d : ℤ) : ℚ)) / ((d - qk a b c d : ℤ) : ℚ) =
      ((a : ℚ) / (d : ℚ) - shadow a b c d + 1) / (2 - shadow a b c d) := by sorry
