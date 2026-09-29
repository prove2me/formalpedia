-- Prove2me | solution 1 for lean_workbook_plus_44726
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:25.669597+00:00
-- url     : https://prove2.me/submissions/2cfb8ac3-b0dc-4170-a5ad-926dc3651193

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x * z ^ 5 + x ^ 5 * y + y ^ 5 * z ≥ (1 / 3) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) ^ 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
