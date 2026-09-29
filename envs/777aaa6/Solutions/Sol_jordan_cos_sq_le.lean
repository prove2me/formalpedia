-- Prove2me | solution 1 for jordan_cos_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T12:05:55.934289+00:00
-- url     : https://prove2.me/submissions/475e2353-81b1-4094-8cd4-2cd90bbfa326

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Real

theorem solution : jordan_cos_sq_le := by
  intro d hd
  have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdr_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hpi := Real.pi_pos
  -- π/(2d) ∈ [0, π/2]
  have h0 : (0 : ℝ) ≤ Real.pi / (2 * d) := by positivity
  have h2 : Real.pi / (2 * (d : ℝ)) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left (le_of_lt hpi) (by norm_num) ?_
    linarith
  -- Jordan: 2/π · π/(2d) ≤ sin(π/(2d)).
  have hjordan := Real.mul_le_sin h0 h2
  -- Simplify LHS: 2/π · π/(2d) = 1/d.
  have hlhs : 2 / Real.pi * (Real.pi / (2 * (d : ℝ))) = 1 / (d : ℝ) := by
    field_simp
  rw [hlhs] at hjordan
  -- sin(π/(2d)) ≥ 1/d ≥ 0, so sin² ≥ 1/d².
  have hsin_sq : (1 / (d : ℝ))^2 ≤ (Real.sin (Real.pi / (2 * d)))^2 := by
    apply sq_le_sq'
    · linarith [hjordan, (by positivity : (0:ℝ) ≤ 1/(d:ℝ))]
    · exact hjordan
  -- cos² = 1 - sin² ≤ 1 - 1/d².
  have hpythag := Real.sin_sq_add_cos_sq (Real.pi / (2 * (d : ℝ)))
  have h1d : (1 / (d : ℝ))^2 = 1 / (d : ℝ)^2 := by field_simp
  linarith [hsin_sq, hpythag, h1d]
