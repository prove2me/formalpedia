-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.sum_bad_real_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:47.577411+00:00
-- url     : https://prove2.me/submissions/e53e85e5-c98b-40a6-a9a2-a8542cd9e318

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_sum_inv_odd
import Theorems.Thm_HyperbolicBerggrenGeodesics_sum_inv_sq_odd

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
theorem solution(K : ℕ) :
    (((∑ d ∈ oddDivs K, (K / d + 1) * (2 * K / d) : ℕ)) : ℝ)
      ≤ (K : ℝ) ^ 2 / 2 + 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  rw [Nat.cast_sum]
  set g : ℕ → ℝ := fun d => ((K : ℝ) / (d : ℝ) + 1) * (2 * (K : ℝ) / (d : ℝ)) with hg
  -- each term is bounded by its real counterpart
  have hterm : ∀ d ∈ oddDivs K, (((K / d + 1) * (2 * K / d) : ℕ) : ℝ) ≤ g d := by
    intro d hd
    rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    push_cast
    have h1 : (((K / d : ℕ)) : ℝ) ≤ (K : ℝ) / d := Nat.cast_div_le
    have h2 : (((2 * K / d : ℕ)) : ℝ) ≤ (2 * (K : ℝ)) / d := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 * K) (n := d)
      push_cast at this
      linarith
    have h3 : (0 : ℝ) ≤ (((2 * K / d : ℕ)) : ℝ) := Nat.cast_nonneg _
    rw [hg]
    nlinarith [Nat.cast_nonneg (α := ℝ) (K / d)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- reindex the odd divisors as `2i+3`
  have hsub : oddDivs K ⊆ (Finset.range K).image (fun i => 2 * i + 3) := by
    intro d hd
    rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
    refine Finset.mem_image.2 ⟨(d - 3) / 2, Finset.mem_range.2 (by omega), ?_⟩
    omega
  have hnonneg : ∀ d ∈ (Finset.range K).image (fun i => 2 * i + 3),
      d ∉ oddDivs K → (0 : ℝ) ≤ g d := by
    intro d hd _
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    rw [hg]
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg) ?_
  have hinj : Set.InjOn (fun i => 2 * i + 3) (Finset.range K) := by
    intro x _ y _ h
    dsimp only at h
    omega
  rw [Finset.sum_image hinj]
  -- split into the `1/d²` and `1/d` parts
  have hsplit : ∀ i ∈ Finset.range K,
      g (2 * i + 3)
        = 2 * (K : ℝ) ^ 2 * (1 / (2 * (i : ℝ) + 3) ^ 2)
          + 2 * (K : ℝ) * (1 / (2 * (i : ℝ) + 3)) := by
    intro i _
    have hi : ((2 * i + 3 : ℕ) : ℝ) = 2 * (i : ℝ) + 3 := by push_cast; ring
    rw [hg]
    simp only [hi]
    have hpos : (0 : ℝ) < 2 * (i : ℝ) + 3 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_inv_sq_odd K
  have h2 := sum_inv_odd K
  have hs : 0 ≤ Real.sqrt (2 * (K : ℝ) + 1) := Real.sqrt_nonneg _
  have hb1 : 2 * (K : ℝ) ^ 2 * (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2)
      ≤ (K : ℝ) ^ 2 / 2 := by
    have hnn : (0 : ℝ) ≤ 2 * (K : ℝ) ^ 2 := by positivity
    have : (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3) ^ 2) ≤ 1 / 4 := by
      have : (0 : ℝ) < 4 * (K : ℝ) + 4 := by positivity
      linarith [h1, one_div_pos.2 this]
    nlinarith
  have hb2 : 2 * (K : ℝ) * (∑ i ∈ Finset.range K, (1 : ℝ) / (2 * (i : ℝ) + 3))
      ≤ 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) := by
    have hnn : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
    nlinarith [h2]
  linarith
