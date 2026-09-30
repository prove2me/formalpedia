-- Prove2me | solution 2 for lean_workbook_plus_10605
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:58.176038+00:00
-- url     : https://prove2.me/submissions/849577fa-cdf9-4613-b741-a50276462ca1

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9) := by
  intro h
  have := h 0 0 0
  norm_num at this
