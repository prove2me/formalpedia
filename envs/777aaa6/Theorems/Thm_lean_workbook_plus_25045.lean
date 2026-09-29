-- Prove2me | Theorems.Thm_lean_workbook_plus_25045
-- name    : lean_workbook_plus_25045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6649a16f-aa2e-44ff-a0d9-77d6ecf79b26
-- statement:
--   Therefore, $ \boxed{\frac{2}{11} < p < \frac{3}{11}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25045 (p : ℝ) (hp : p > 0 ∧ p < 1) (h : 2 / 11 < p ∧ p < 3 / 11) : 2 / 11 < p ∧ p < 3 / 11   :=  by sorry
