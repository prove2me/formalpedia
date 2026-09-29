-- Prove2me | solution 1 for lean_workbook_plus_60300
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:46.346411+00:00
-- url     : https://prove2.me/submissions/e6a253a1-ab9e-4584-b3ec-000464e2fe02

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a = 3), (5 * a ^ 3 + 3 * a) ^ (1 / 3) + (5 * b ^ 3 + 3 * b) ^ (1 / 3) + (5 * c ^ 3 + 3 * c) ^ (1 / 3) ≥ 6) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
