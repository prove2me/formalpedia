-- Prove2me | solution 1 for lean_workbook_plus_81357
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:50.784297+00:00
-- url     : https://prove2.me/submissions/6d0434a9-628d-45e9-9cdd-e07c8fc1dfe0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ (∀ a : ℝ, (a+1)^2/(a^2+1)^2 ≤ 1/(a^2-a+1)) := by
  intro h
  have h2 := h 2
  norm_num at h2
