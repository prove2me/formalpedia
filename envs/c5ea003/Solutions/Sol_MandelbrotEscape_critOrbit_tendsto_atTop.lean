-- Prove2me | solution 1 for MandelbrotEscape.critOrbit_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:26:28.603236+00:00
-- url     : https://prove2.me/submissions/2de8143d-1237-4432-86eb-0d5fc9d3d6ce

-- Sol generated from Novelty/MandelbrotQuadraticEscape.lean
import Mathlib
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_MandelbrotEscape_critOrbit_succ
import Theorems.Thm_MandelbrotEscape_qmap_norm_lower

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
lemma critOrbit_growth (c : ℂ) (hc : 2 < ‖c‖) (n : ℕ) :
    ‖c‖ ≤ ‖critOrbit c (n + 1)‖ ∧ ‖c‖ * (‖c‖ - 1) ^ n ≤ ‖critOrbit c (n + 1)‖ := by
  induction' n with n ih;
  · simp +decide [ critOrbit, qmap ];
  · -- Using the induction hypothesis and the triangle inequality, we have:
    have h_step : ‖critOrbit c (n + 2)‖ ≥ ‖critOrbit c (n + 1)‖^2 - ‖c‖ := by
      simpa only [ critOrbit_succ ] using qmap_norm_lower c _;
    constructor <;> ring_nf at * <;> nlinarith [ sq_nonneg ( ‖critOrbit c ( n + 1 )‖ - ‖c‖ ) ]

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
theorem solution(c : ℂ) (hc : 2 < ‖c‖) :
    Filter.Tendsto (fun n => ‖critOrbit c n‖) Filter.atTop Filter.atTop := by
  -- We use the fact that ‖c‖ > 2 to show that ‖critOrbit c n‖ Filter.eventually grows at least as fast as a geometric sequence with ratio ‖c‖ - 1 > 1.
  have h_geometric : Filter.Tendsto (fun n => ‖c‖ * (‖c‖ - 1) ^ n) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt ( by linarith ) );
  rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ];
  exact Filter.tendsto_atTop_mono ( fun n => by simpa using ( critOrbit_growth c hc n ).2 ) h_geometric
