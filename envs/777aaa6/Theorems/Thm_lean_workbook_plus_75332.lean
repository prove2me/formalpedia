-- Prove2me | Theorems.Thm_lean_workbook_plus_75332
-- name    : lean_workbook_plus_75332
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b99f3256-2b63-46f1-ab18-e1065996c3d5
-- statement:
--   Let $x$ be real number . Prove that \n $$x^2+(\frac{1}{x}-1)^2+\frac{1}{(x-1)^2}\geq 5$$ $$ x^2+(\frac{4}{x}-1)^2+\frac{1}{(x-1)^2} \geq 6$$ $$x^2+(\frac{1}{x}-1)^2+(\frac{1}{x}+1)^ 2\geq 2(\sqrt 2+1)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75332 : ∀ x : ℝ, x^2 + (1/x - 1)^2 + 1/(x-1)^2 ≥ 5 ∧ x^2 + (4/x - 1)^2 + 1/(x-1)^2 ≥ 6 ∧ x^2 + (1/x - 1)^2 + (1/x + 1)^2 ≥ 2 * (Real.sqrt 2 + 1)   :=  by sorry
