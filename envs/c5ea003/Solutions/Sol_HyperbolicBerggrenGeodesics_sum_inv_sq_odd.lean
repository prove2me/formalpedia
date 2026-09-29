-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.sum_inv_sq_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:39:50.331426+00:00
-- url     : https://prove2.me/submissions/77cf979e-f9f5-4d5e-b479-55847d2356e0

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII

/-!
# Hyperbolic–Pythagorean Geodesics, cycle III: quadratic ball growth

The first cycle proved that the hyperbolic ball of radius `R` around `i` contains at least
`e^{R-2} - 1` Berggren nodes, and conjectured (sub-conjecture **C1-lite**) the true order
`e^{2R}`: the number of nodes should grow like the *hypotenuse*, not like its square root.

This file proves that conjecture.  The obstruction is arithmetic, not geometric: one has to
produce quadratically many *coprime* pairs of opposite parity, which requires a sieve.

## Main results

* `card_multiples_Ioc` : the exact count of multiples of `k` in an interval `(a, b]`.
* `sum_inv_sq_odd`, `sum_inv_odd` : two telescoping estimates,
  `∑_{i<n} 1/(2i+3)² ≤ 1/4` and `∑_{i<n} 1/(2i+3) ≤ √(2n+1) - 1`.
* `card_seedBox_lower` : **the sieve bound.**  For `K ≥ 256` the box
  `{m even, 2K < m ≤ 4K} × {n odd, 1 ≤ n ≤ 2K}` contains at least `K²/4` Euclid seeds.
* `hyperbolic_ball_quadratic_growth` : **C1-lite, closed.**  For every `K ≥ 256` the
  hyperbolic ball of radius `R = log K + 2` around the base point contains at least
  `e^{2R}/300` distinct Berggren nodes.  Since every node with hypotenuse `c` sits at
  distance `≈ ½ log c`, this is the true order of growth, and it shows definitively that
  geodesic search through the Berggren tree cannot beat exhaustive search: the ball that
  is guaranteed to contain a colliding pair for `N` already contains `≍ N` nodes.
-/

open HyperbolicBerggrenGeodesics

open Real UpperHalfPlane

noncomputable section

/-! ## Part A. Counting multiples -/



/-! ## Part B. Two telescoping estimates -/



/-! ## Part C. The sieve -/












/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/





/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/





open HyperbolicBerggrenGeodesics in
theorem solution(n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2 ≤ 1 / 4 - 1 / (4 * (n : ℝ) + 4) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have key : (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2
        ≤ 1 / (4 * (n : ℝ) + 4) - 1 / (4 * ((n : ℝ) + 1) + 4) := by
      have e : 1 / (4 * (n : ℝ) + 4) - 1 / (4 * ((n : ℝ) + 1) + 4)
          = 4 / ((4 * (n : ℝ) + 4) * (4 * (n : ℝ) + 8)) := by
        field_simp
        ring
      rw [e]
      refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
      nlinarith [sq_nonneg ((n : ℝ))]
    push_cast
    linarith [ih]
