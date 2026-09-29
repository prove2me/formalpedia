-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.card_seedBox_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:45:34.10471+00:00
-- url     : https://prove2.me/submissions/24538212-2e03-4e6b-a5ee-0f21354c3e43

-- Sol generated from Geometry/HyperbolicBerggrenDensity.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenDensity
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesicsII
import Theorems.Thm_HyperbolicBerggrenGeodesics_bad_subset
import Theorems.Thm_HyperbolicBerggrenGeodesics_card_evenBox_filter
import Theorems.Thm_HyperbolicBerggrenGeodesics_card_multiples_Ioc
import Theorems.Thm_HyperbolicBerggrenGeodesics_sum_bad_real_le

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





theorem card_evenBox (K : ℕ) : (evenBox K).card = K := by
  rw [evenBox, card_multiples_Ioc 2 (2 * K) (4 * K) (by omega)]
  omega

theorem card_oddBox (K : ℕ) : (oddBox K).card = K := by
  have hall : (Finset.Icc 1 (2 * K)).card = 2 * K := by simp
  have hhalf : ((Finset.Icc 1 (2 * K)).filter (fun n => 2 ∣ n)).card = K := by
    have hIcc : Finset.Icc 1 (2 * K) = Finset.Ioc 0 (2 * K) := by
      ext x; simp [Nat.lt_iff_add_one_le]
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (2 * K)) (p := fun n => 2 ∣ n)
  rw [oddBox]
  omega



theorem card_oddBox_filter (K d : ℕ) :
    ((oddBox K).filter (fun n => d ∣ n)).card ≤ 2 * K / d := by
  have hsub : (oddBox K).filter (fun n => d ∣ n)
      ⊆ (Finset.Ioc 0 (2 * K)).filter (fun n => d ∣ n) := by
    intro x hx
    rw [oddBox, Finset.filter_filter, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hx.2.2⟩
  have := Finset.card_le_card hsub
  rwa [Nat.Ioc_filter_dvd_card_eq_div] at this


/-- The sieve inequality in `ℕ`. -/
theorem card_bad_le (K : ℕ) :
    ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card
      ≤ ∑ d ∈ oddDivs K, (K / d + 1) * (2 * K / d) := by
  refine le_trans (Finset.card_le_card bad_subset) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [oddDivs, Finset.mem_filter, Finset.mem_Icc] at hd
  rw [Finset.card_product]
  exact Nat.mul_le_mul (card_evenBox_filter hd.2) (card_oddBox_filter K d)

/-! ## Part D. From the sieve to a quadratic lower bound -/



/-! ## Part E. Quadratic volume growth of hyperbolic balls (C1-lite, closed) -/





/-! ## Part F. Cycle IV: the matching upper bound, and exact semiprime splitting -/





open HyperbolicBerggrenGeodesics in
theorem solution{K : ℕ} (hK : 256 ≤ K) : (K : ℝ) ^ 2 / 4 ≤ ((seedBox K).card : ℝ) := by
  have hKR : (256 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  -- total = good + bad
  have htotal : (evenBox K ×ˢ oddBox K).card = K * K := by
    rw [Finset.card_product, card_evenBox, card_oddBox]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := evenBox K ×ˢ oddBox K) (p := fun p => Nat.Coprime p.1 p.2)
  have hgood : (seedBox K).card
      + ((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card = K * K := by
    rw [seedBox]
    omega
  have hbad : (((evenBox K ×ˢ oddBox K).filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ)
      ≤ (K : ℝ) ^ 2 / 2 + 2 * K * Real.sqrt (2 * K + 1) := by
    refine le_trans ?_ (sum_bad_real_le K)
    exact_mod_cast card_bad_le K
  -- `2 K √(2K+1) ≤ K²/4` for `K ≥ 256`
  have hsq : Real.sqrt (2 * (K : ℝ) + 1) ≤ (K : ℝ) / 8 := by
    rw [show (K : ℝ) / 8 = Real.sqrt (((K : ℝ) / 8) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hfinal : 2 * (K : ℝ) * Real.sqrt (2 * (K : ℝ) + 1) ≤ (K : ℝ) ^ 2 / 4 := by
    nlinarith
  have hcast : ((seedBox K).card : ℝ) + (((evenBox K ×ˢ oddBox K).filter
      (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (K : ℝ) * K := by
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hgood
  nlinarith [hbad, hfinal, hcast]
