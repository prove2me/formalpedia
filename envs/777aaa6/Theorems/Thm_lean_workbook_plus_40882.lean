-- Prove2me | Theorems.Thm_lean_workbook_plus_40882
-- name    : lean_workbook_plus_40882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/11d2554c-06f2-4fb1-9d71-58e01c86420b
-- statement:
--   Minimize $ Z=X+3Y$\n\nsubject to\n\n $ 2x + y≤10$\n\n $ 5X + 2y ≥ 20$\n\n $ -X + 2y ≥ 0$\n\n $ x≥0, y≥0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40882 (x y : ℝ) : (2*x + y ≤ 10 ∧ 5*x + 2*y ≥ 20 ∧ -x + 2*y ≥ 0 ∧ x >= 0 ∧ y >= 0) → x + 3*y >= 7   :=  by sorry
