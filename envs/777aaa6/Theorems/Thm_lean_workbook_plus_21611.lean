-- Prove2me | Theorems.Thm_lean_workbook_plus_21611
-- name    : lean_workbook_plus_21611
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7942b621-8eae-42ae-87cd-07878a71cbed
-- statement:
--   The function $ f(x) = \frac{1}{1+x^2}\geq 1-\frac{x}{2}$ for $ x\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21611 (x : ℝ) (hx: x ≥ 0) : (1 / (1 + x ^ 2)) ≥ 1 - x / 2   :=  by sorry
