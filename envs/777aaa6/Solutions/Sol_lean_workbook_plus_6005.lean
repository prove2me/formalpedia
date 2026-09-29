-- Prove2me | solution 1 for lean_workbook_plus_6005
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:07.994353+00:00
-- url     : https://prove2.me/submissions/6cb6fc87-fee9-4478-9825-524dc473e966

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (2016 ^ 167 = (2000 + 17) ^ 167) := by
  push_neg
  norm_num at *
