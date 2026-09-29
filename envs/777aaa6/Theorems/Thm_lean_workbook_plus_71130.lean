-- Prove2me | Theorems.Thm_lean_workbook_plus_71130
-- name    : lean_workbook_plus_71130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c514a30d-eacf-459e-889c-6212f2afe77d
-- statement:
--   Find all real numbers $x$ such that $x^4 + 4x^3 + 6x^2 + 4x + 1 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71130 (x : ℝ) : x^4 + 4*x^3 + 6*x^2 + 4*x + 1 = 0 ↔ x = -1   :=  by sorry
