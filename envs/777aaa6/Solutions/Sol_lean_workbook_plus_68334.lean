-- Prove2me | solution 1 for lean_workbook_plus_68334
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:54:54.159448+00:00
-- url     : https://prove2.me/submissions/fd14abb8-b5d9-4855-b0a9-7840cfb43ad4

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, 2*a^2 + 2*b^2 + 2*c^2 + a^2*b^2 + b^2*c^2 + c^2*a^2 ≥ 72) := by
  intro h
  have := h 0 0 0
  norm_num at this
