-- Prove2me | Theorems.Thm_lean_workbook_plus_42070
-- name    : lean_workbook_plus_42070
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e90e2ae2-8640-47cf-9d86-b86db8b1592c
-- statement:
--   Prove that $3(ab-ac+bc)^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42070 (a b c : ℝ) : 3 * (a * b - a * c + b * c) ^ 2 ≥ 0   :=  by sorry
