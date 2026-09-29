-- Prove2me | Theorems.Thm_lean_workbook_plus_54116
-- name    : lean_workbook_plus_54116
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/148fb178-dcf9-4440-ba24-84edbf03b00d
-- statement:
--   Cauchy gives : \n\n $\left(\frac{2}{a}+\frac{3}{b}+\frac{1}{c}\right)(2a+3b+c)\ge (2+3+1)^2$ \nIt follows that the minimum is 36.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54116 : ∀ a b c : ℝ, (2 / a + 3 / b + 1 / c) * (2 * a + 3 * b + c) ≥ 36   :=  by sorry
