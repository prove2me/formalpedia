-- Prove2me | Theorems.Thm_lean_workbook_plus_52760
-- name    : lean_workbook_plus_52760
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0b8c364b-2ffe-4700-b5da-ba0d06212293
-- statement:
--   Prove: $\cos^2A\cos^2B+\cos^2B\cos^2C+\cos^2C\cos^2A\le\frac{1}{4}(\cos^2A+\cos^2B+\cos^2C)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52760 : ∀ A B C : ℝ, cos A ^ 2 * cos B ^ 2 + cos B ^ 2 * cos C ^ 2 + cos C ^ 2 * cos A ^ 2 ≤ 1 / 4 * (cos A ^ 2 + cos B ^ 2 + cos C ^ 2)   :=  by sorry
