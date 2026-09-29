-- Prove2me | Theorems.Thm_lean_workbook_plus_12477
-- name    : lean_workbook_plus_12477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/eadce3df-f254-46b5-9d85-4d9923acc359
-- statement:
--   Probability you have it and are tested positive: $\frac{1}{100}\cdot\frac{99}{100}=\frac{99}{10000}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12477 (h : 0 < 100) : (1 / 100 * 99 / 100 : ℚ) = 99 / 10000   :=  by sorry
