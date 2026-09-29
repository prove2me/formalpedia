-- Prove2me | solution 1 for lean_workbook_plus_24261
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:54.947968+00:00
-- url     : https://prove2.me/submissions/7f5cb6fe-b67a-444b-8045-8d8d8dd72983

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p q : ℝ, p^2 - 6 * p + q^2 - 2 * q + 6 ≥ (p - 3)^2) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
