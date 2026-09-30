-- Prove2me | solution 1 for lean_workbook_plus_61082
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:10.260615+00:00
-- url     : https://prove2.me/submissions/68ec7ba5-f1b8-4fd6-950c-240288c6428c

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ∧ 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3) := by
  rintro a b c ⟨ha, hb, hc⟩
  constructor
  · nlinarith [mul_nonneg (add_pos ha hb).le (sq_nonneg (a - b))]
  · nlinarith [mul_nonneg (add_pos ha hb).le (sq_nonneg (a - b)),
      mul_nonneg (add_pos hb hc).le (sq_nonneg (b - c)),
      mul_nonneg (add_pos ha hc).le (sq_nonneg (a - c)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
