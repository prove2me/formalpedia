-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.hyperbolic_ball_quadratic_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:02:58.184768+00:00
-- url     : https://prove2.me/submissions/c4e7c50f-28ad-45d4-a552-ba49a9908fc1

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_card_seedBox_lower
import Theorems.Thm_HyperbolicBerggrenGeodesics_hpoint_injective
import Theorems.Thm_HyperbolicBerggrenGeodesics_nodePoint_dist_le

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


theorem nodePoint_injOn (K : ℕ) : Set.InjOn nodePoint (seedBox K) := by
  intro p hp q hq hpq
  have hsp := mem_seedBox_isSeed (K := K) (by simpa using hp)
  have hsq := mem_seedBox_isSeed (K := K) (by simpa using hq)
  have hp0 : 0 < p.1 := lt_trans hsp.pos hsp.lt
  have hq0 : 0 < q.1 := lt_trans hsq.pos hsq.lt
  rw [nodePoint, nodePoint, dif_pos hp0, dif_pos hq0] at hpq
  obtain ⟨h1, h2⟩ := hpoint_injective hp0 hq0 hpq
  exact Prod.ext h1 h2



/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/





open HyperbolicBerggrenGeodesics in
theorem solution{K : ℕ} (hK : 256 ≤ K) :
    ∃ (R : ℝ) (S : Finset ℍ), R = Real.log K + 2 ∧
      Real.exp (2 * R) / 300 ≤ (S.card : ℝ) ∧
      ∀ z ∈ S, dist z UpperHalfPlane.I ≤ R := by
  classical
  refine ⟨Real.log K + 2, (seedBox K).image nodePoint, rfl, ?_, ?_⟩
  · have hcard : (((seedBox K).image nodePoint).card : ℝ) = ((seedBox K).card : ℝ) := by
      rw [Finset.card_image_of_injOn (nodePoint_injOn K)]
    rw [hcard]
    refine le_trans ?_ (card_seedBox_lower hK)
    have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hexp : Real.exp (2 * (Real.log K + 2)) = Real.exp 4 * (K : ℝ) ^ 2 := by
      rw [show 2 * (Real.log K + 2) = 4 + 2 * Real.log K by ring, Real.exp_add,
        show (2 : ℝ) * Real.log K = Real.log ((K : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
    rw [hexp]
    have h4 : Real.exp 4 ≤ 75 := by
      have h1 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
      have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h3 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
      rw [h2]
      nlinarith [h3]
    nlinarith [sq_nonneg ((K : ℝ))]
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    exact nodePoint_dist_le hK hp
