-- Prove2me | Theorems.Thm_lean_workbook_plus_6047
-- name    : lean_workbook_plus_6047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1987139f-40fe-40f3-abf1-73d0d5ad0f57
-- statement:
--   In a $\triangle ABC $ , prove that $\frac{cos^2A}{sin^2B+sin^2C}+\frac{cos^2B}{sin^2C+sin^2A}+\frac{cos^2C}{sin^2A+sin^2B}\ge \frac{1}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6047 : ∀ A B C : ℝ, (cos A ^ 2 / (sin B ^ 2 + sin C ^ 2)) + (cos B ^ 2 / (sin C ^ 2 + sin A ^ 2)) + (cos C ^ 2 / (sin A ^ 2 + sin B ^ 2)) ≥ 1 / 2   :=  by sorry
