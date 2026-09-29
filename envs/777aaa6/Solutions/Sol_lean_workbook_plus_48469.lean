-- Prove2me | solution 1 for lean_workbook_plus_48469
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:32:34.55353+00:00
-- url     : https://prove2.me/submissions/048b2b00-12e3-4988-a176-d8a265920f3a

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (0 < (3 ^ 29 - 2 ^ 31) / (3 ^ 29 + 2 ^ 29) ∧ (3 ^ 29 - 2 ^ 31) / (3 ^ 29 + 2 ^ 29) < 1) := by
  push_neg
  norm_num at *
