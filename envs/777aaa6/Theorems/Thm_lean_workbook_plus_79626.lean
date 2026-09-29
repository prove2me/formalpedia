-- Prove2me | Theorems.Thm_lean_workbook_plus_79626
-- name    : lean_workbook_plus_79626
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/401126bb-95e8-409f-8ae4-0326658ebe24
-- statement:
--   Prove that $3x^3 + 3x^2 + 3x + 3 > 0$ for $ x > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79626 (x : ℝ) (hx : x > 1) : 3 * x ^ 3 + 3 * x ^ 2 + 3 * x + 3 > 0   :=  by sorry
