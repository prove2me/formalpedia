-- Prove2me | solution 1 for lean_workbook_plus_8013
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-06T01:59:47.250618+00:00
-- url     : https://prove2.me/submissions/7df8d5a4-0419-46e1-b431-462c14c21a7b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ¬ (∀ a b c d : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 ≥
    4 * a * b * c * d + 2 * (a - b) * (b - c) * (c - d) * (d - a)) := by
  intro h
  have hh := h 1 (-1) 1 (-1)
  norm_num at hh
  exact (show ¬ ((4 : ℝ) + 32 ≤ 1 + 1 + 1 + 1) by norm_num) hh
