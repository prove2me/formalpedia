-- Prove2me | Theorems.Thm_lean_workbook_plus_1885
-- name    : lean_workbook_plus_1885
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3953b176-0356-450f-ae73-974abaaf1ae8
-- statement:
--   Prove that $\sin\left(2A\right)+\sin\left(2B\right)+\sin\left(2C\right)=4\sin A\sin B\sin C$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1885 (A B C : ℝ) (hA : 0 < A ∧ A <= π ∧ B <= π ∧ C <= π ∧ A + B + C = π) : Real.sin (2 * A) + Real.sin (2 * B) + Real.sin (2 * C) = 4 * Real.sin A * Real.sin B * Real.sin C   :=  by sorry
