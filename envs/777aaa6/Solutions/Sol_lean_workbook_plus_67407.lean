-- Prove2me | solution 1 for lean_workbook_plus_67407
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:27:03.249279+00:00
-- url     : https://prove2.me/submissions/add55681-f36d-4daa-ae00-7fe996399411

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : (a + c) * (b ^ 2 + a * c) = 4 * a) :
    abs (b ^ 2 + c ^ 2 - 4) ≥ 2 * b * c := by
  have hm : a * (2 * b * c) ≤ a * (4 - b ^ 2 - c ^ 2) := by
    nlinarith only [h₁, mul_nonneg h₀.2.2.le (sq_nonneg (a - b))]
  have hbound := le_of_mul_le_mul_left hm h₀.1
  linarith [neg_le_abs (b ^ 2 + c ^ 2 - 4)]
