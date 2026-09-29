-- Prove2me | solution 1 for lean_workbook_plus_13278
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:04.959862+00:00
-- url     : https://prove2.me/submissions/aeaa7eea-a5eb-4212-a69f-3d38ecb2f775

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ {p q r : ℝ}, p^4 * r^2 + p^2 * q^4 + q^2 * r^4 ≥ p^4 * q * r + p * q^4 * r + p * q * r^4) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
