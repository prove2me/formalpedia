-- Prove2me | Theorems.Thm_lean_workbook_plus_51902
-- name    : lean_workbook_plus_51902
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/78fd424c-b422-4aed-9b49-5098dc51a558
-- statement:
--   Verify that $f(-1) = 6$ for the function $f(x)=-\frac{4}{3}x^{2}-\frac{14}{3}x+\frac{8}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51902 (f : ℝ → ℝ) (f_def : f = fun x => -(4/3)*x^2 -(14/3)*x + (8/3)) : f (-1) = 6   :=  by sorry
