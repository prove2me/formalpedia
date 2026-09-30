-- Prove2me | solution 1 for lean_workbook_plus_8456
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:50.03329+00:00
-- url     : https://prove2.me/submissions/2156477d-4891-46e0-8aae-ebf3da3f829f

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c d : ℝ, a * b * c * d * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 4 + 3 / 2 * a * b * c * d * (a + b + c + d) * (a + b + c + d - 4)) := by
  intro h
  have := h (-2) (-2) 2 2
  ring_nf at this
  norm_num at this
