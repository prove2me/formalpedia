-- Prove2me | Definitions.Def_Shared_HigherPythagorean_HyperbolicBoundary
-- name    : Shared_HigherPythagorean_HyperbolicBoundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:55:56.899456+00:00
-- url     : https://prove2.me/theorems/bfa5846d-d956-43d1-b706-0d03b5b8495d
-- title:
--   Aether Catalog definitions — Shared_HigherPythagorean_HyperbolicBoundary
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HigherPythagorean.HyperbolicBoundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HigherPythagorean/HyperbolicBoundary.lean by skeleton subtraction
import Mathlib
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

namespace HigherPythagorean

/-! ## Boundary sphere -/


/-- The *shadow* of a node: the sum of its normalised space coordinates. -/
def shadow (a b c d : ℤ) : ℚ := ((a : ℚ) + (b : ℚ) + (c : ℚ)) / (d : ℚ)



/-! ## Algebraicity of the growth constant -/




end HigherPythagorean


