-- Prove2me | solution 1 for lean_workbook_plus_40555
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:45:16.895113+00:00
-- url     : https://prove2.me/submissions/b207a4bc-7920-44fa-b980-2694fa2691f0

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c + 2 = a * b * c), 1 / a + 1 / b + 1 / c ≥ 4 * (a + b + c)) := by
  push_neg
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
