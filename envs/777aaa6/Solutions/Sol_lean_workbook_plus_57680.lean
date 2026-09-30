-- Prove2me | solution 1 for lean_workbook_plus_57680
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:40.264544+00:00
-- url     : https://prove2.me/submissions/6ce13ffe-f944-42fb-8ef9-1e89d00684f3

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y z : ℝ, x + y + z = 1 → x > 0 ∧ y > 0 ∧ z > 0 → x^2 * (x + y) * (x + z) + y^2 * (y + x) * (y + z) + z^2 * (z + x) * (z + y) ≥ 1 + (x + y)^2 + (x + z)^2 + (y + z)^2) := by
  intro h
  have := h (1/3) (1/3) (1/3) (by norm_num) ⟨by norm_num, by norm_num, by norm_num⟩
  norm_num at this
