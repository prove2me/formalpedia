-- Prove2me | solution 1 for lean_workbook_plus_11795
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:16.299668+00:00
-- url     : https://prove2.me/submissions/2f985c1f-cc79-4820-a6c0-6a2dfa483848

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (2005^(1002^2) * (41^2 + 18^2) = 2005^(2005)) := by
  push_neg
  norm_num at *
  omega
