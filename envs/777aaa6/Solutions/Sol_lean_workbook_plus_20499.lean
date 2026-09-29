-- Prove2me | solution 1 for lean_workbook_plus_20499
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:42.886817+00:00
-- url     : https://prove2.me/submissions/33b426fc-06f1-4200-a25c-cd6534a4c7b6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, (3 * n - 20 * (n / 10)) % 7 = 0) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
