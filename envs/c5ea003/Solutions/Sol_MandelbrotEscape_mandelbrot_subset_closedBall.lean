-- Prove2me | solution 1 for MandelbrotEscape.mandelbrot_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:28.808407+00:00
-- url     : https://prove2.me/submissions/b4c5310c-0f84-4cc8-a2e6-c36028b409c2

-- Sol generated from Novelty/MandelbrotQuadraticEscape.lean
import Mathlib
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_MandelbrotEscape_critOrbit_tendsto_atTop

/-!
# The Mandelbrot Set: Quadratic Recurrence and the Escape Radius

The Mandelbrot set `M` is the set of complex parameters `c` for which the *critical orbit*
`0, c, c²+c, …` of the quadratic map `f_c(z) = z² + c` stays bounded.

This file develops the elementary — but genuinely quantitative — dynamics of the recurrence
`z_{n+1} = z_n² + c` and proves the classical **escape-radius theorem**: if `‖c‖ > 2` then the
critical orbit diverges to infinity, so `M` is contained in the closed disk of radius `2`.

The heart of the argument is a geometric lower bound on the orbit:
`‖c‖·(‖c‖-1)ⁿ ≤ ‖f_c^{(n+1)}(0)‖`, which forces divergence because `‖c‖ - 1 > 1`.

We also record two concrete membership facts: `0 ∈ M` and `-1 ∈ M` (the orbit of `-1` is the
`2`-cycle `0, -1, 0, -1, …`), while every `c` with `‖c‖ > 2` lies outside `M`.
-/

open MandelbrotEscape

open Filter
open scoped Topology






/-
Reverse triangle inequality specialised to the quadratic map:
`‖z‖² - ‖c‖ ≤ ‖z² + c‖`.
-/

/-
The key growth invariant.  If `‖c‖ > 2`, then for every `n` the `(n+1)`-st iterate of the
critical orbit is at least `‖c‖` in norm, and in fact grows geometrically at rate `‖c‖ - 1`.
-/

/-
**Escape theorem.**  If `‖c‖ > 2`, the norm of the critical orbit tends to infinity.
-/

/-
**Escape radius / a-priori bound for the Mandelbrot set.**
Every parameter in the Mandelbrot set has norm at most `2`.
-/

/-
Any parameter of norm `> 2` escapes, hence lies outside the Mandelbrot set.
-/

/-
The origin is in the Mandelbrot set (its critical orbit is constantly `0`).
-/

/-
The critical orbit of `c = -1` is the `2`-cycle `0, -1, 0, -1, …`.
-/

/-
`c = -1` lies in the Mandelbrot set (its orbit is a bounded `2`-cycle).
-/

/-
A concrete escaping parameter: `c = 3` is not in the Mandelbrot set.
-/


open MandelbrotEscape in
theorem solution{c : ℂ} (hc : c ∈ Mandelbrot) : ‖c‖ ≤ 2 := by
  obtain ⟨B, hB⟩ := hc;
  -- By contradiction, assume ‖c‖ > 2.
  by_contra h_contra;
  exact absurd ( critOrbit_tendsto_atTop c ( not_le.mp h_contra ) ) ( by exact fun h => by have := h.eventually_gt_atTop B; obtain ⟨ n, hn ⟩ := this.exists; linarith [ hB n ] )
