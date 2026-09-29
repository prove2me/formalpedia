-- Prove2me | solution 1 for lean_workbook_plus_45633
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:48.296124+00:00
-- url     : https://prove2.me/submissions/4709e013-3ec6-49db-948d-19c47a67fee4

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (2 : ℝ) ≥ (1 + x * y) / (2 * z ^ 2 + 1 + x * y) + (1 + y * z) / (2 * x ^ 2 + 1 + y * z) + (1 + z * x) / (2 * y ^ 2 + 1 + z * x)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *
