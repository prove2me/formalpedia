-- Prove2me | solution 1 for lean_workbook_plus_7009
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:56.779428+00:00
-- url     : https://prove2.me/submissions/174dbc22-9650-4278-ab0d-17acaa8877b1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (2^10 + 5^12 = 125^4 + 4 * 4^4 ∧
  125^4 + 4 * 4^4 = (125^2 + 2 * 4^2 + 2 * (5 * 4)) * (125^2 + 2 * 4^2 - 2 * (5 * 4))) := by
  push_neg
  norm_num at *
