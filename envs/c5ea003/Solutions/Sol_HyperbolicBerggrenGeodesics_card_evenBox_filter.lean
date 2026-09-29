-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.card_evenBox_filter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:39:49.369342+00:00
-- url     : https://prove2.me/submissions/269d2991-725c-404b-a6a3-453bdde08546

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_add_div_le_add_div
import Theorems.Thm_HyperbolicBerggrenGeodesics_card_multiples_Ioc

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
theorem solution{K d : ℕ} (hd : ¬ 2 ∣ d) :
    ((evenBox K).filter (fun m => d ∣ m)).card ≤ K / d + 1 := by
  have hcop : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hd
  have hset : (evenBox K).filter (fun m => d ∣ m)
      = (Finset.Ioc (2 * K) (4 * K)).filter (fun m => 2 * d ∣ m) := by
    rw [evenBox, Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h2, hdx⟩
      exact hcop.mul_dvd_of_dvd_of_dvd h2 hdx
    · intro h
      exact ⟨dvd_trans ⟨d, rfl⟩ h, dvd_trans ⟨2, by ring⟩ h⟩
  rw [hset, card_multiples_Ioc _ _ _ (by omega)]
  have h1 : 4 * K / (2 * d) = 2 * K / d := by
    rw [show 4 * K = 2 * (2 * K) by ring, Nat.mul_div_mul_left _ _ (by omega)]
  have h2 : 2 * K / (2 * d) = K / d := Nat.mul_div_mul_left _ _ (by omega)
  rw [h1, h2]
  have h3 : 2 * K / d ≤ K / d + K / d + 1 := by
    have h := add_div_le_add_div K K d
    rwa [show K + K = 2 * K from (two_mul K).symm] at h
  exact Nat.sub_le_iff_le_add.2 (by linarith)
