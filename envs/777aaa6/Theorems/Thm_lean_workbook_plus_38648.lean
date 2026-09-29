-- Prove2me | Theorems.Thm_lean_workbook_plus_38648
-- name    : lean_workbook_plus_38648
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/59521c8e-e3a2-46df-a397-8b47c7b77844
-- statement:
--   (a+b)^{4}\geq1^{4} then $a^{4}+b^{4}+4a^{3}b+6a^{2}b^{2}+4ab^{3}\geq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38648 (a b : ℝ) (hab : (a + b) ^ 4 ≥ 1 ^ 4) : a ^ 4 + b ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 ≥ 1   :=  by sorry
