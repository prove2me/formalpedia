-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.bad_subset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:15.685079+00:00
-- url     : https://prove2.me/submissions/9c07c66b-7b2a-4fb4-bc37-6c8fd3b9acce

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
theorem solution{K : ℕ} :
    ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2))
      ⊆ (oddDivs K).biUnion (fun d =>
          ((evenBox K).filter (fun m => d ∣ m)) ×ˢ ((oddBox K).filter (fun n => d ∣ n))) := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, hcop⟩ := hp
  have hn' := hn
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn'
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn'
  set d := Nat.gcd p.1 p.2 with hd
  have hdm : d ∣ p.1 := Nat.gcd_dvd_left _ _
  have hdn : d ∣ p.2 := Nat.gcd_dvd_right _ _
  have hdle : d ≤ p.2 := Nat.le_of_dvd (by omega) hdn
  have hdodd : ¬ 2 ∣ d := fun h2 => hn3 (h2.trans hdn)
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hdn
    omega
  have hd1 : d ≠ 1 := hcop
  have hd3 : 3 ≤ d := by
    rcases Nat.lt_or_ge d 3 with h | h
    · interval_cases d
      · exact absurd rfl hd0
      · exact absurd rfl hd1
      · exact absurd ⟨1, rfl⟩ hdodd
    · exact h
  refine Finset.mem_biUnion.2 ⟨d, ?_, ?_⟩
  · rw [oddDivs, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd3, by omega⟩, hdodd⟩
  · exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hm, hdm⟩, Finset.mem_filter.2 ⟨hn, hdn⟩⟩
