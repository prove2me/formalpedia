-- Prove2me | solution 1 for lean_workbook_plus_73917
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:09:26.645285+00:00
-- url     : https://prove2.me/submissions/8d56c1e7-ba9e-490e-8073-b93d6af893fb

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c d : ℝ,
    a^3 + b^3 + c^3 + d^3 ≥ (a + b + c + d)^3) := by
  intro h
  have hbad := h 1 1 1 1
  norm_num at hbad
