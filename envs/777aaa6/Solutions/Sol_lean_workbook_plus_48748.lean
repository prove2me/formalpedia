-- Prove2me | solution 1 for lean_workbook_plus_48748
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:47.979386+00:00
-- url     : https://prove2.me/submissions/96c5e41d-484b-40f8-9f81-e9b2a5a7c2e5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^4 * b^2 + 1) + (a^2 * b^4 + 1) + (a^4 * c^2 + 1) + (a^2 * c^4 + 1) + (b^4 * c^2 + 1) + (b^2 * c^4 + 1) + (a^3 * b^3 + a^3 * c^3) + (b^3 * a^3 + b^3 * c^3) + (c^3 * a^3 + c^3 * b^3) ≥ 2 * a^2 * b + 2 * a * b^2 + 2 * a^2 * c + 2 * a * c^2 + 2 * b^2 * c + 2 * b * c^2 + 2 * a^3 + 2 * b^3 + 2 * c^3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
