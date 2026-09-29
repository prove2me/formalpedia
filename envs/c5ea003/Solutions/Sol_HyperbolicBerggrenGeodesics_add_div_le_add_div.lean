-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.add_div_le_add_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:15.199804+00:00
-- url     : https://prove2.me/submissions/d8948daf-dd61-47b4-9fc2-fafd1f748ff3

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
theorem solution(a b k : ℕ) : (a + b) / k ≤ a / k + b / k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · omega
  · have hma := Nat.mod_lt a h
    have hmb := Nat.mod_lt b h
    have hsplit : a + b = k * (a / k + b / k) + (a % k + b % k) := by
      have hka := Nat.div_add_mod a k
      have hkb := Nat.div_add_mod b k
      have : k * (a / k + b / k) = k * (a / k) + k * (b / k) := by ring
      omega
    rw [hsplit, Nat.mul_add_div h]
    have : (a % k + b % k) / k < 2 := (Nat.div_lt_iff_lt_mul h).2 (by omega)
    omega
