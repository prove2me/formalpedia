-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.nodePoint_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:00:20.755209+00:00
-- url     : https://prove2.me/submissions/d5f00ecc-4901-4c48-80d8-3cc372102353

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_dist_le_half_log_two_hypotenuse

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







/-- Every element of the coprime box is a Euclid seed. -/
theorem mem_seedBox_isSeed {K : ℕ} {p : ℕ × ℕ} (hp : p ∈ seedBox K) : IsSeed p.1 p.2 := by
  rw [seedBox, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, hcop⟩ := hp
  rw [evenBox, Finset.mem_filter, Finset.mem_Ioc] at hm
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hm
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
  refine ⟨by omega, by omega, hcop, ?_⟩
  omega





/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/





/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/





open HyperbolicBerggrenGeodesics in
theorem solution{K : ℕ} (hK : 256 ≤ K) {p : ℕ × ℕ} (hp : p ∈ seedBox K) :
    dist (nodePoint p) UpperHalfPlane.I ≤ Real.log K + 2 := by
  have hs := mem_seedBox_isSeed hp
  have hp0 : 0 < p.1 := lt_trans hs.pos hs.lt
  rw [nodePoint, dif_pos hp0]
  have hb := dist_le_half_log_two_hypotenuse hs.pos hs.lt
  refine le_trans hb ?_
  -- the box forces `m ≤ 4K` and `n ≤ 2K`, so `2 (c+1) ≤ 42 K² ≤ K² e⁴`
  rw [seedBox, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hm, hn⟩, -⟩ := hp
  rw [evenBox, Finset.mem_filter, Finset.mem_Ioc] at hm
  rw [oddBox, Finset.mem_filter, Finset.mem_Icc] at hn
  have hmle : (p.1 : ℝ) ≤ 4 * K := by exact_mod_cast hm.1.2
  have hnle : (p.2 : ℝ) ≤ 2 * K := by exact_mod_cast hn.1.2
  have hm0 : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg _
  have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hc : 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) ≤ 42 * (K : ℝ) ^ 2 := by nlinarith
  have hexp : (42 : ℝ) ≤ Real.exp 4 := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
    have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7182818283 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1 4
    rw [h2]
    nlinarith [h3]
  have hle : 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) ≤ Real.exp 4 * (K : ℝ) ^ 2 := by
    nlinarith
  have hpos : (0 : ℝ) < 2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1) := by positivity
  have hlog : Real.log (2 * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 + 1))
      ≤ 4 + 2 * Real.log K := by
    have hR : Real.log (Real.exp 4 * (K : ℝ) ^ 2) = 4 + 2 * Real.log K := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow]
      push_cast; ring
    have h1 := Real.log_le_log hpos hle
    rwa [hR] at h1
  linarith
