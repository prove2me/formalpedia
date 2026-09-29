-- Prove2me | solution 1 for lean_workbook_plus_18178
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:58.482506+00:00
-- url     : https://prove2.me/submissions/65e04f5a-ed0e-4c5b-b489-b3ddac4bddbb

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z), x ^ 3 + y ^ 3 + z ^ 3 + 2 * x * y * z ≥ x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
