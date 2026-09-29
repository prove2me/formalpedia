-- Prove2me | solution 1 for lean_workbook_plus_11231
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:27.786693+00:00
-- url     : https://prove2.me/submissions/9171e005-db20-40a4-9261-44e7939d79ba

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (4 ∣ 5^9 - 1 ∧ 8 ∣ 5^9 - 1) := by
  push_neg
  norm_num at *
