-- Prove2me | Theorems.Thm_lean_workbook_plus_45775
-- name    : lean_workbook_plus_45775
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3adae251-e746-4f3b-beb2-769633da9649
-- statement:
--   Find the limit \n $\lim_{x\\rightarrow 0}\\frac{e^x \\sin x -x^2}{x^3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45775 (x : ℝ) : (exp x * Real.sin x - x ^ 2) / x ^ 3 ≠ 0 ∨ (exp x * Real.sin x - x ^ 2) / x ^ 3 = 0   :=  by sorry
