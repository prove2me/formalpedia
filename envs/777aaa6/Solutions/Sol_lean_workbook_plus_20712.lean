-- Prove2me | solution 1 for lean_workbook_plus_20712
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:39.184347+00:00
-- url     : https://prove2.me/submissions/bb6af65a-1535-4c78-ab3d-f521bcca1394

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 → a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c) ≤ 3 / 4) := by
  rintro a b c ⟨ha, hb, hc⟩
  have h1 : 0 < 2 * a + b + c := by linarith
  have h2 : 0 < a + 2 * b + c := by linarith
  have h3 : 0 < a + b + 2 * c := by linarith
  rw [div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (by positivity) h3.ne', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg ha.le (sq_nonneg (b - c)), mul_nonneg hb.le (sq_nonneg (a - c)), mul_nonneg hc.le (sq_nonneg (a - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
