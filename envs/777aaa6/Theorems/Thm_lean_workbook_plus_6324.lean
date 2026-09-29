-- Prove2me | Theorems.Thm_lean_workbook_plus_6324
-- name    : lean_workbook_plus_6324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4e47c716-b509-4ef0-814f-d39d4cef07cc
-- statement:
--   From $y=3x+b$ , we have on the x-axis $(-\frac{b}{3},0)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6324 (x y : ℝ) (b : ℝ) (h₁ : y = 3 * x + b) (h₂ : x = -b / 3) : y = 0   :=  by sorry
