-- Prove2me | solution 1 for lean_workbook_plus_48606
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:21.01914+00:00
-- url     : https://prove2.me/submissions/10ace90b-5032-49bb-9f51-fb5c83e0663b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x + y + z)^3 + 5 * x * y * z ≥ 4 * (x + y) * (y + z) * (z + x)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
