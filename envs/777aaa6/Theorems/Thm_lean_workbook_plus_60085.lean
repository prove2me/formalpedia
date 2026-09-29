-- Prove2me | Theorems.Thm_lean_workbook_plus_60085
-- name    : lean_workbook_plus_60085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/51fd9252-62e4-486a-87da-e990e257d4cf
-- statement:
--   Given $y > 1$ and $y(y+1) \leq (x+1)^2$, show that $y(y-1) \leq x^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60085 (x y : ℝ) (h : y > 1) (h' : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2   :=  by sorry
