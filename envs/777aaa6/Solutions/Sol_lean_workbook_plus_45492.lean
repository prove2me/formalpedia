-- Prove2me | solution 1 for lean_workbook_plus_45492
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:47.82993+00:00
-- url     : https://prove2.me/submissions/85b00a48-d4d9-4879-a717-96adc6ff8872

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ 0) (h2: a^2 + b^2 + c^2 + d^2 = 1) : a + b ≥ 1 ∧ 1 ≥ c + d := by
  rcases h with ⟨hab,hbc,hcd,hd⟩
  have hsum := h2
  have hc : 0≤c := le_trans hd hcd
  have hb : 0≤b := le_trans hc hbc
  have ha : 0≤a := le_trans hb hab
  have h1 := mul_nonneg (sub_nonneg.mpr hab) hb
  have h2 := mul_nonneg (sub_nonneg.mpr hbc) (add_nonneg hb hc)
  have h3 := mul_nonneg (sub_nonneg.mpr hcd) (add_nonneg hc hd)
  have h4 := mul_nonneg (sub_nonneg.mpr (le_trans hcd hbc)) (add_nonneg hb hd)
  have h5 := mul_nonneg (sub_nonneg.mpr (le_trans hbc hab)) (add_nonneg ha hc)
  have h6 := mul_nonneg hc (sub_nonneg.mpr hcd)
  have hlo : (1:ℝ)^2≤(a+b)^2 := by nlinarith only [h1,h2,h4,hsum]
  have hup : (c+d)^2≤(1:ℝ)^2 := by nlinarith only [h2,h5,h6,hsum]
  exact ⟨(sq_le_sq₀ (by norm_num) (add_nonneg ha hb)).mp hlo,(sq_le_sq₀ (add_nonneg hc hd) (by norm_num)).mp hup⟩
