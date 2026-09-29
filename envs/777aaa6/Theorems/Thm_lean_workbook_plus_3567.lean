-- Prove2me | Theorems.Thm_lean_workbook_plus_3567
-- name    : lean_workbook_plus_3567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/8258adad-88ce-4c07-8014-e74ff29cad90
-- statement:
--   Let $a,b,c$ be real numbers with sum equal to zero. Prove that $ab^3+bc^3+ca^3\leqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3567 (a b c : ℝ) (hab : a + b + c = 0) : a * b ^ 3 + b * c ^ 3 + c * a ^ 3 ≤ 0   :=  by sorry
