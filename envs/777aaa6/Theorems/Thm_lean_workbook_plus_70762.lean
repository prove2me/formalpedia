-- Prove2me | Theorems.Thm_lean_workbook_plus_70762
-- name    : lean_workbook_plus_70762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/76e42a5e-b183-4c7c-b03b-f03674112d8a
-- statement:
--   Given $a,b,c,d\in\mathbb{R}$ , satisfying the system of equations \n \n \begin{align*}a&=b, \\ c&=d,\end{align*} is logically equivalent to satisfying the system of equations \n \n \begin{align*}a+c&=b+d, \\ a-c&=b-d.\end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70762 (a b c d : ℝ) : a = b ∧ c = d ↔ a + c = b + d ∧ a - c = b - d   :=  by sorry
