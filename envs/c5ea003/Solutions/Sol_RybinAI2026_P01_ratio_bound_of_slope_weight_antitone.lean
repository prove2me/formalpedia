-- Prove2me | solution 1 for RybinAI2026.P01.ratio_bound_of_slope_weight_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:11:17.608527+00:00
-- url     : https://prove2.me/submissions/123ae2eb-4819-4247-a121-3ef808da3bb6

import Mathlib

theorem solution (G : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hanti : AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    G b / G a ≤ (1 + (Real.sqrt a)⁻¹) / (1 + (Real.sqrt b)⁻¹) := by
  have hweight := hanti (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) hab
  have hden : 0 < 1 + (Real.sqrt b)⁻¹ := by positivity
  apply (div_le_div_iff₀ (hGpos a ha) hden).2
  simpa [mul_comm] using hweight
