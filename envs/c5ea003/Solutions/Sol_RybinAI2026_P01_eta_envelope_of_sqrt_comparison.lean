-- Prove2me | solution 1 for RybinAI2026.P01.eta_envelope_of_sqrt_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:37:57.096976+00:00
-- url     : https://prove2.me/submissions/3dcd19f3-dc6c-47ea-b962-10fc31012a71

import Mathlib

theorem solution (t ψ : ℝ) (ht : 0 < t) (hψ : 0 < ψ)
    (hhi : 1 < t → 1 / Real.sqrt t ≤ ψ)
    (hlo : t < 1 → ψ ≤ 1 / Real.sqrt t) :
    (if t = 1 then (1 : ℝ) / 6 else
      (1 - ψ) / (2 * (t - 1) * ψ)) ≤
        1 / (2 * (1 + Real.sqrt t)) := by
  by_cases heq : t = 1
  · norm_num [heq]
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    by_cases hgt : 1 < t
    · have hprod : 1 ≤ ψ * Real.sqrt t := (div_le_iff₀ hs).1 (hhi hgt)
      have hd : 0 < 2 * (t - 1) * ψ := by positivity
      have he : 0 < 2 * (1 + Real.sqrt t) := by positivity
      rw [if_neg heq, div_le_div_iff₀ hd he]
      nlinarith [mul_le_mul_of_nonneg_right hprod (show 0 ≤ 2 * (1 + Real.sqrt t) by positivity)]
    · have hlt : t < 1 := by
        rcases lt_or_eq_of_le (le_of_not_gt hgt) with h | h
        · exact h
        · exact (heq h).elim
      have hprod : ψ * Real.sqrt t ≤ 1 := (le_div_iff₀ hs).1 (hlo hlt)
      have hd : 2 * (t - 1) * ψ < 0 := by
        have hpos : 0 < 2 * (1 - t) * ψ :=
          mul_pos (mul_pos (by norm_num) (sub_pos.mpr hlt)) hψ
        nlinarith
      have he : 0 < 2 * (1 + Real.sqrt t) := by positivity
      rw [if_neg heq, div_le_iff_of_neg hd]
      have hmul : (1 / (2 * (1 + Real.sqrt t))) * (2 * (t - 1) * ψ) =
          (2 * (t - 1) * ψ) / (2 * (1 + Real.sqrt t)) := by ring
      rw [hmul, div_le_iff₀ he]
      nlinarith [mul_le_mul_of_nonneg_right hprod
        (show 0 ≤ 2 * (1 + Real.sqrt t) by positivity)]
