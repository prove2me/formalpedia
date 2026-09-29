-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.card_multiples_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:38:30.812703+00:00
-- url     : https://prove2.me/submissions/fc812ec7-16c4-4722-80e8-d4a5be89939a

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
theorem solution(k a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun x => k ∣ x)).card = b / k - a / k := by
  have hsub : (Finset.Ioc 0 a).filter (fun x => k ∣ x)
      ⊆ (Finset.Ioc 0 b).filter (fun x => k ∣ x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans hab⟩, hx.2⟩
  have hEq : (Finset.Ioc a b).filter (fun x => k ∣ x)
      = ((Finset.Ioc 0 b).filter (fun x => k ∣ x)) \ ((Finset.Ioc 0 a).filter (fun x => k ∣ x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, not_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨by omega, h2⟩, h3⟩, by intro hc; omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      by_contra hc
      exact absurd h3 (h4 ⟨h1, by omega⟩)
  rw [hEq, Finset.card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div]
