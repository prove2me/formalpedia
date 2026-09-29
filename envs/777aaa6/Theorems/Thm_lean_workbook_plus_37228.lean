-- Prove2me | Theorems.Thm_lean_workbook_plus_37228
-- name    : lean_workbook_plus_37228
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/616f3634-79e0-4dbf-b036-3a2640c58d43
-- statement:
--   Prove that $\frac{2x}{1+x^2} \leq 1$ for all $x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37228 (x : ℝ) (hx : 0 < x) : (2 * x) / (1 + x ^ 2) ≤ 1   :=  by sorry
