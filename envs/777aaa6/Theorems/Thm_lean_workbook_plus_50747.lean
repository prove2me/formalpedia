-- Prove2me | Theorems.Thm_lean_workbook_plus_50747
-- name    : lean_workbook_plus_50747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ab670096-cd69-4071-aaaa-0b56265ecf35
-- statement:
--   Prove that $(x_1x_2+x_2x_3+x_3x_1)^2 \geq 3x_1x_2x_3(x_1+x_2+x_3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50747 (x1 x2 x3 : ℝ) : (x1 * x2 + x2 * x3 + x3 * x1) ^ 2 ≥ 3 * x1 * x2 * x3 * (x1 + x2 + x3)   :=  by sorry
