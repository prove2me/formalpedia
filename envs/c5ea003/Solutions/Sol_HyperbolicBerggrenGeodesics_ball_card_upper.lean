-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.ball_card_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:27:56.007552+00:00
-- url     : https://prove2.me/submissions/f322d022-e0ec-43d1-864c-786ee2affe74

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_dist_ge_half_log_hypotenuse

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
theorem solution{R : ℝ} (hR : 0 ≤ R) (S : Finset (ℕ × ℕ))
    (hseed : ∀ p ∈ S, IsSeed p.1 p.2)
    (hball : ∀ p ∈ S, ∀ h : 0 < p.1, dist (hpoint p.1 p.2 h) UpperHalfPlane.I ≤ R) :
    (S.card : ℝ) ≤ 4 * Real.exp (2 * R) := by
  classical
  set M : ℕ := ⌊Real.exp R⌋₊ with hM
  have hMle : (M : ℝ) ≤ Real.exp R := Nat.floor_le (Real.exp_pos R).le
  -- every node in the ball has both coordinates at most `M`
  have hsub : S ⊆ Finset.range (M + 1) ×ˢ Finset.range (M + 1) := by
    intro p hp
    have hs := hseed p hp
    have hp0 : 0 < p.1 := lt_trans hs.pos hs.lt
    have hd := hball p hp hp0
    have hlow := dist_ge_half_log_hypotenuse hs.pos hs.lt
    have hc0 : (0 : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
      have : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
      positivity
    have hlog : Real.log ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ 2 * R := by linarith
    have hcle : (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ Real.exp (2 * R) := by
      have := Real.exp_le_exp.2 hlog
      rwa [Real.exp_log hc0] at this
    have hm2 : (p.1 : ℝ) ^ 2 ≤ (Real.exp R) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by positivity
      have hsq : (Real.exp R) ^ 2 = Real.exp (2 * R) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [hsq]
      linarith
    have hmle : (p.1 : ℝ) ≤ Real.exp R := by
      nlinarith [Nat.cast_nonneg (α := ℝ) p.1, (Real.exp_pos R).le]
    have hmM : p.1 ≤ M := Nat.le_floor hmle
    have hnM : p.2 ≤ M := le_trans hs.lt.le hmM
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hcard : S.card ≤ (M + 1) * (M + 1) := by
    simpa [Finset.card_product] using Finset.card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) := by
    have : ((S.card : ℕ) : ℝ) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have he1 : (1 : ℝ) ≤ Real.exp R := Real.one_le_exp hR
  have hsq : (Real.exp R) ^ 2 = Real.exp (2 * R) := by
    rw [← Real.exp_nat_mul]; ring_nf
  nlinarith [Nat.cast_nonneg (α := ℝ) M]
