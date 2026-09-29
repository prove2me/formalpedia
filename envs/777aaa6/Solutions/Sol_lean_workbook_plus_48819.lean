-- Prove2me | solution 1 for lean_workbook_plus_48819
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:04.320044+00:00
-- url     : https://prove2.me/submissions/0db1527c-db06-41f7-b414-1d6b8fe126ff

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, x^5 + x^2 + 1 = (x^2 + x + 1) * (x^3 + 1) - x^2 * (x^2 + x + 1)) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
