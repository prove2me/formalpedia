-- Prove2me | solution 1 for lean_workbook_plus_49510
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:27:47.865838+00:00
-- url     : https://prove2.me/submissions/6f4b6a37-a884-4dc6-b1e8-18d87075ec0b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution : ∀ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1 → x^2*y^2*(x^2+y^2) ≤ 2 := by
  intro x y h
  rcases h with ⟨hx,hy,hxy⟩
  have hx1 : x ≤ 1 := by linarith
  have hy1 : y ≤ 1 := by linarith
  have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  have hy2 : y^2 ≤ 1 := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hy1)]
  have hp : x^2*y^2 ≤ (1:ℝ)*1 := mul_le_mul hx2 hy2 (sq_nonneg y) (by norm_num)
  have hs : x^2+y^2 ≤ (2:ℝ) := by linarith
  calc
    x^2*y^2*(x^2+y^2) ≤ (1*1)*2 := mul_le_mul hp hs (by positivity) (by norm_num)
    _ = 2 := by norm_num
