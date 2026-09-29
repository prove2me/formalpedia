-- Prove2me | Theorems.Thm_lean_workbook_plus_71666
-- name    : lean_workbook_plus_71666
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3dc8241e-b178-4627-858c-4f2316cd7c1b
-- statement:
--   Let $\sin C=0$ and $\sin B=-\sin A$, prove that $\cos 2A+\cos2B+\cos 2C = 3-4\sin^2A$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71666 : ∀ A B C : ℝ, sin C = 0 ∧ sin B = -sin A → cos 2*A + cos 2*B + cos 2*C = 3 - 4 * sin A ^ 2   :=  by sorry
