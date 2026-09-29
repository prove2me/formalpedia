-- Prove2me | solution 1 for lean_workbook_plus_46257
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:56.433252+00:00
-- url     : https://prove2.me/submissions/ca257004-2887-4e26-beaa-08d8bd3680a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ ((3 / 4 : ℝ) ^ 2 * 2 + 2 ^ 2 * (1 / 4) + (1 / 4) ^ 2 * (3 / 4) ≥ 1 / 3 * (3 / 4 + 2 + 1 / 4) * (3 / 4 * 2 + 2 * 1 / 4 + 1 / 4 * 3 / 4)) := by
  push_neg
  norm_num at *
