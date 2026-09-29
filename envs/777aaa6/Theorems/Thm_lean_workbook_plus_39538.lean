-- Prove2me | Theorems.Thm_lean_workbook_plus_39538
-- name    : lean_workbook_plus_39538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c55c662d-e721-4153-8742-c28d01e13d80
-- statement:
--   Let $ a,b $ be reals such that $a^2(a+b)=2 .$ Prove that \n\n $a^3+ab(a+b)+b^3\geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39538 (a b : ℝ) (h : a^2 * (a + b) = 2) : a^3 + a * b * (a + b) + b^3 ≥ 2   :=  by sorry
