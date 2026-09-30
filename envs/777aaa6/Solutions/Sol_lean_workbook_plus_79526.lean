-- Prove2me | solution 1 for lean_workbook_plus_79526
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:48.21219+00:00
-- url     : https://prove2.me/submissions/d1c90501-40bb-4a76-b493-e995fa7331ba

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∃ x : ℕ → ℝ,
    2*x 1 = x 5 ^ 2 - 23 ∧ 4*x 2 = x 1 ^ 2 + 7 ∧ 6*x 3 = x 2 ^ 2 + 14 ∧
    8*x 4 = x 3 ^ 2 + 23 ∧ 10*x 5 = x 4 ^ 2 + 34 := by
  refine ⟨fun n => n, ?_⟩
  norm_num
