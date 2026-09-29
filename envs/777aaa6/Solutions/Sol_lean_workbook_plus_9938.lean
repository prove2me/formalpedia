-- Prove2me | solution 1 for lean_workbook_plus_9938
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:08.855038+00:00
-- url     : https://prove2.me/submissions/cf924ae2-8d44-4816-a3cc-5c069d2247ee

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 4 * (a * b + b * c + c * a) + a * b * c ≥ 19) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
