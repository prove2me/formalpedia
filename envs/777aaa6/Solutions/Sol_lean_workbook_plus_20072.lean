-- Prove2me | solution 1 for lean_workbook_plus_20072
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:25.791632+00:00
-- url     : https://prove2.me/submissions/e1d25408-b01f-48ee-a661-ae52f863e488

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x^3 * y + y^3 * z + z^3 * x)^2 ≥ (x^3 * y + y^3 * z + z^3 * x) * (x * y^3 + y * z^3 + z * x^3) ∧ (x^3 * y + y^3 * z + z^3 * x) * (x * y^3 + y * z^3 + z * x^3) ≥ (x^2 * y^2 + y^2 * z^2 + z^2 * x^2)^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
