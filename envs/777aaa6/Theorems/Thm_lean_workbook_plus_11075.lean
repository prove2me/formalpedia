-- Prove2me | Theorems.Thm_lean_workbook_plus_11075
-- name    : lean_workbook_plus_11075
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a516fd7f-d7c6-4dd8-8c47-358873dc74ac
-- statement:
--   This factorises into: \n\n $ (2a - 2b + c)^2 + (b - 2c + 2d)^2 + (a - c + d)^2 + (b - c)^2 + 1/2(2a -b)^2 + 1/2(b - 2d)^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11075 (a b c d : ℝ) : (2 * a - 2 * b + c) ^ 2 + (b - 2 * c + 2 * d) ^ 2 + (a - c + d) ^ 2 + (b - c) ^ 2 + (1 / 2) * (2 * a - b) ^ 2 + (1 / 2) * (b - 2 * d) ^ 2 ≥ 0   :=  by sorry
