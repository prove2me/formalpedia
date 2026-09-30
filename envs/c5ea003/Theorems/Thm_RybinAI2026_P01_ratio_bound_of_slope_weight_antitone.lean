-- Prove2me | Theorems.Thm_RybinAI2026_P01_ratio_bound_of_slope_weight_antitone
-- name    : RybinAI2026.P01.ratio_bound_of_slope_weight_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:06:49.905429+00:00
-- url     : https://prove2.me/theorems/bd885d15-2047-4252-968c-3c09307d36af
-- title:
--   Antitone slope weight bounds endpoint ratios
-- statement:
--   If G is positive and G(t)(1+1/sqrt(t)) is antitone on the positive reals, then for positive a≤b the ratio G(b)/G(a) is at most the ratio of the corresponding slope weights. This is the endpoint form used in the high-parameter diagonal pair branch.
-- source:
--   Endpoint consequence of the integrated slope envelope in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.ratio_bound_of_slope_weight_antitone (G : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hanti : AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    G b / G a ≤ (1 + (Real.sqrt a)⁻¹) / (1 + (Real.sqrt b)⁻¹) := by
  sorry
