-- Prove2me | solution 1 for lean_workbook_plus_78104
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:39:35.770303+00:00
-- url     : https://prove2.me/submissions/906d072b-0c58-440b-885d-8ec337ad0070

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, (6 - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 ≤ 24 - 5 * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  intro h
  have := h 0 0 0
  norm_num at this
