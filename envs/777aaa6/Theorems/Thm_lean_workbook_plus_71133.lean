-- Prove2me | Theorems.Thm_lean_workbook_plus_71133
-- name    : lean_workbook_plus_71133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/603b7796-6a41-4566-b8dc-39ff6303d3d8
-- statement:
--   If $a,b\geq1$ , prove that $a^5+b^5\geq (a+b)a^2b^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71133 (a b : ℝ) (hab : a ≥ 1 ∧ b ≥ 1) : a^5 + b^5 ≥ (a + b) * a^2 * b^2   :=  by sorry
