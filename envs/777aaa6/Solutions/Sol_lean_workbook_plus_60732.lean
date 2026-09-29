-- Prove2me | solution 1 for lean_workbook_plus_60732
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:21:06.813573+00:00
-- url     : https://prove2.me/submissions/a29b3a1b-77c0-40a5-ae11-5372a0ca23e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ ((1^4 + 2^4 + 3^4 + 4^4 + 5^4) % 6 = 3) := by
  push_neg
  norm_num at *
