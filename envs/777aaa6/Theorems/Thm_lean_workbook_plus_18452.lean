-- Prove2me | Theorems.Thm_lean_workbook_plus_18452
-- name    : lean_workbook_plus_18452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e418204d-3ebe-49c7-be26-08539bb26e49
-- statement:
--   Let $ x,y$ be positive real numbers satisfying $ \frac {1}{x(x+5y)}+ \frac {1}{y(y+5x)}= 1$ . Prove that $xy\le \frac {1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18452 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y) (h : 1 / (x * (x + 5 * y)) + 1 / (y * (y + 5 * x)) = 1) : x * y ≤ 1 / 3   :=  by sorry
