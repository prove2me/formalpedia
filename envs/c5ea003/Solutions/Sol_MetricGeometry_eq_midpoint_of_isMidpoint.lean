-- Prove2me | solution 1 for MetricGeometry.eq_midpoint_of_isMidpoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T18:32:29.985729+00:00
-- url     : https://prove2.me/submissions/12bb89e4-86ee-472e-8735-f64272f5c135

import Definitions.Def_metric_npc_cone

open MetricGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m x y : E) (h : IsMidpoint m x y) : m = midpoint ℝ x y := by
  obtain ⟨h1, h2⟩ := h
  rw [dist_eq_norm] at h1 h2
  have hxy : ‖x - y‖ = ‖x - m‖ + ‖m - y‖ := by
    rw [h1, h2, dist_eq_norm]; ring
  have hsum : (x - m) + (m - y) = x - y := by abel
  have hkey : (inner ℝ (x - m) (m - y) : ℝ) = ‖x - m‖ * ‖m - y‖ := by
    have e1 : ‖x - y‖ ^ 2 = ‖x - m‖ ^ 2 + 2 * inner ℝ (x - m) (m - y) + ‖m - y‖ ^ 2 := by
      rw [← hsum, norm_add_sq_real]
    rw [hxy] at e1
    nlinarith [e1]
  rw [inner_eq_norm_mul_iff_real] at hkey
  have hnorm : ‖x - m‖ = ‖m - y‖ := by rw [h1, h2, dist_eq_norm]
  rcases eq_or_ne ‖m - y‖ 0 with h0 | h0
  · have hx : x = m := sub_eq_zero.mp (by rw [← norm_eq_zero, hnorm]; exact h0)
    have hy : m = y := sub_eq_zero.mp (by rw [← norm_eq_zero]; exact h0)
    rw [← hx, ← hy] at *
    simp [midpoint_self]
  · rw [hnorm] at hkey
    have hab : x - m = m - y := smul_right_injective E h0 hkey
    rw [sub_eq_sub_iff_add_eq_add] at hab
    have htwo : (2 : ℝ) ≠ 0 := two_ne_zero
    refine smul_right_injective E htwo ?_
    show (2 : ℝ) • m = (2 : ℝ) • midpoint ℝ x y
    rw [two_smul ℝ m, two_smul ℝ (midpoint ℝ x y), midpoint_add_self]
    exact hab.symm
