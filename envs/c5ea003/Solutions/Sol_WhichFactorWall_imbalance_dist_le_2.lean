-- Prove2me | solution 2 for WhichFactorWall.imbalance_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:29:22.863186+00:00
-- url     : https://prove2.me/submissions/87697287-069b-4e79-9cb3-b2c16128593d

import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
open WhichFactorWall Real Set in
theorem solution {η p q : ℝ} (hη : 0 < η) (hη2 : η < 2⁻¹)
    (hp : p ∈ Icc (0 : ℝ) (2⁻¹ - η)) (hq : q ∈ Icc (0 : ℝ) (2⁻¹ - η)) :
    (log (2⁻¹ + η) - log (2⁻¹ - η)) * |p - q| ≤ |binEntropy p - binEntropy q| := by
  -- tangent-line bound from concavity: `(v - u)(log(1-v) - log v) ≤ H v - H u` for `0 ≤ u ≤ v ≤ 1/2`
  have htan : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 2⁻¹ →
      (v - u) * (log (1 - v) - log v) ≤ binEntropy v - binEntropy u := by
    intro u v hu huv hv
    rcases huv.eq_or_lt with h | h
    · subst h
      simp
    · have hv0 : v ≠ 0 := (lt_of_le_of_lt hu h).ne'
      have hv1 : v ≠ 1 := ne_of_lt (by linarith)
      have hd := strictConcave_binEntropy.concaveOn.deriv_le_slope
        ⟨hu, by linarith⟩ ⟨by linarith, by linarith⟩ h (differentiableAt_binEntropy hv0 hv1)
      rw [deriv_binEntropy, slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hd
      linarith [hd]
  -- on `(0, 1/2 - η]` the log-ratio `log(1-v) - log v` is at least `log(1/2+η) - log(1/2-η)`
  have hrat : ∀ v : ℝ, 0 < v → v ≤ 2⁻¹ - η →
      log (2⁻¹ + η) - log (2⁻¹ - η) ≤ log (1 - v) - log v := by
    intro v hv0 hv
    have h1 : log (2⁻¹ + η) ≤ log (1 - v) := log_le_log (by linarith) (by linarith)
    have h2 : log v ≤ log (2⁻¹ - η) := log_le_log hv0 hv
    linarith
  have hc : 0 ≤ log (2⁻¹ + η) - log (2⁻¹ - η) := by
    have := log_le_log (by linarith : (0 : ℝ) < 2⁻¹ - η) (by linarith : 2⁻¹ - η ≤ 2⁻¹ + η)
    linarith
  -- reduce to `p ≤ q` by symmetry
  have key : ∀ u v : ℝ, u ∈ Icc (0 : ℝ) (2⁻¹ - η) → v ∈ Icc (0 : ℝ) (2⁻¹ - η) → u ≤ v →
      (log (2⁻¹ + η) - log (2⁻¹ - η)) * |u - v| ≤ |binEntropy u - binEntropy v| := by
    intro u v hu hv huv
    rcases huv.eq_or_lt with h | h
    · subst h
      simp
    · have hv0 : 0 < v := lt_of_le_of_lt hu.1 h
      have ht := htan u v hu.1 huv (by linarith [hv.2])
      have hr := hrat v hv0 hv.2
      have hvu : 0 ≤ v - u := by linarith
      have hmono := mul_le_mul_of_nonneg_left hr hvu
      rw [abs_sub_comm u v, abs_of_nonneg hvu, abs_sub_comm,
        abs_of_nonneg (by nlinarith [mul_nonneg hvu hc])]
      nlinarith
  rcases le_total p q with h | h
  · exact key p q hp hq h
  · rw [abs_sub_comm p q, abs_sub_comm (binEntropy p)]
    exact key q p hq hp h
