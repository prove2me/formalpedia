-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_QuarticFiber
-- name    : Algebra_AbstractAlgebra_QuarticFiber
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:12.636292+00:00
-- url     : https://prove2.me/theorems/04449e95-fc95-4af8-ba7b-ede6064f663b
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_QuarticFiber
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.QuarticFiber`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/QuarticFiber.lean by skeleton subtraction
import Mathlib
/-
# Perfect Cuboid — Quartic Fiber Reduction

Starting from the perfect cuboid surface equation `w² = u² + v² - 1`
with square constraints `u² - 1 = (y/x)²` and `v² - 1 = (z/x)²`,
we apply the standard rational parametrizations
  `u = (r² + 1)/(2r)`,  `v = (s² + 1)/(2s)`
and derive the quartic fiber equation:
  `W² = r²s⁴ + (r⁴ + 1)s² + r²`
where `W = 2rsw`.

**Note:** The prompt originally stated the quartic as
`W² = r²s⁴ + (r⁴ - 2r² + 1)s² + r²`, but this is incorrect.
The correct coefficient of `s²` is `r⁴ + 1`, not `(r² - 1)² = r⁴ - 2r² + 1`.
The error arose from a miscalculation when clearing denominators.

## Main results

* `cuboid_parametrized_quartic` — the algebraic reduction from the surface
  equation to the quartic fiber.
* `quarticFiber` — the defining predicate for the quartic fiber curve.
* `quarticFiber_symmetric` — the quartic is even in `s`.
* `conicFiber` — descent to a conic in `t = s²`.
-/

namespace PerfectCuboid

/-! ## The quartic fiber equation -/

/-- The quartic fiber curve: `W² = r²s⁴ + (r⁴ + 1)s² + r²`.
For fixed rational `r ≠ 0`, this is a quartic curve in `(s, W)`. -/
def quarticFiber (r s W : ℚ) : Prop :=
  W ^ 2 = r ^ 2 * s ^ 4 + (r ^ 4 + 1) * s ^ 2 + r ^ 2

/-
**Quartic fiber reduction.**
If `(r, s, w)` satisfy the perfect cuboid surface equation through the
standard Pythagorean parametrization, then `(s, 2rsw)` lies on the
quartic fiber curve.
-/



/-- **Conic descent.** Setting `t = s²`, the quartic fiber becomes the
conic `W² = r²t² + (r⁴ + 1)t + r²` in `(t, W)`. -/
def conicFiber (r t W : ℚ) : Prop :=
  W ^ 2 = r ^ 2 * t ^ 2 + (r ^ 4 + 1) * t + r ^ 2


/-
**Discriminant of the conic fiber.**
The discriminant of the quadratic `r²t² + (r⁴+1)t + r² - W²` in `t` is
`(r⁴+1)² - 4r²(r² - W²)`. Using the conic fiber relation, this simplifies
to a perfect square.
-/

end PerfectCuboid


