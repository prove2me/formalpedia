-- Prove2me | solution 1 for lean_workbook_plus_64968
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:46.931588+00:00
-- url     : https://prove2.me/submissions/ca99a66f-d29d-4e54-9cd4-34d7345589c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (3 * (x - 1) ^ 2 * (-3 * x ^ 10 + 34 * x ^ 9 - 157 * x ^ 8 + 444 * x ^ 7 - 1061 * x ^ 6 + 1970 * x ^ 5 - 1803 * x ^ 4 + 256 * x ^ 3 + 216 * x ^ 2 + 144 * x + 216)) / (8 * x ^ 4 * (3 - x) ^ 4) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
